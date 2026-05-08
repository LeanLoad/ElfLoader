/-
Layout planning — base-free.

Each PT_LOAD `Segment` lifts to a `SegmentPlan` whose page math is
precomputed once and stored: `pageVaddr`, `pageLength`, `pageInset`,
`fileOverlayLen`, `fileOffset`, `partialBssLen`, `prot`. Every offset
is relative to `base = 0`; the materializer adds the chosen base
when emitting structured slots.

Hierarchy:
  • `SegmentPlan` — one PT_LOAD with all loader-view fields stored.
  • `ElfPlan`     — one elf's `SegmentPlan`s, its `objectSpan`, plus
                    a proof that the page-aligned ranges don't
                    overlap (`segmentsSorted`).
  • `LoadPlan`    — every elf's `ElfPlan` plus the cumulative
                    `totalSpan` (the `len` for `mmapAnonAlloc`).

`LoadPlan.ofElfs` builds the whole tree in one pass and validates
page-aligned non-overlap per elf — failure is rare (modern
toolchains never emit overlapping page ranges) but possible in
principle, so the validation is part of construction. Once a
`LoadPlan` exists, `assignBases base lp` is total: it stacks each
elf by `alignUp objectSpan 0x1000` from the IO-supplied base.

Spec: gabi 07 § Program Header (page-aligned mmap views, base
assignment, span over loadable segments).
-/

import LeanLoad.Plan.Align
import LeanLoad.Elaborate.Segment
import LeanLoad.Elaborate.Elf
import LeanLoad.Parse.Structs

namespace LeanLoad.Plan

open LeanLoad
open LeanLoad.Parse
open LeanLoad.Elaborate (Elf Segment)

-- ============================================================================
-- SegmentPlan — one PT_LOAD with all loader-view fields stored.
-- Base-free: every offset is relative to base = 0.
-- ============================================================================

/-- A `Segment` lifted to the loader's view. All page math is
    precomputed once via `ofSegment`; addresses are relative to
    `base = 0`. The materializer adds the chosen base when emitting
    the per-segment structured slots. -/
structure SegmentPlan where
  /-- Underlying gabi segment. Carries `rela`/`jmprel` for reloc
      planning and the `addrBound` invariant for proofs. -/
  segment        : Segment
  /-- `alignDown vaddr ea` — page-aligned start. -/
  pageVaddr      : UInt64
  /-- Total page-aligned mmap length. -/
  pageLength     : UInt64
  /-- `vaddr − pageVaddr`. Distance from page start to first useful byte. -/
  pageInset      : UInt64
  /-- Page-aligned length of the file-backed overlay. Zero when `filesz = 0`. -/
  fileOverlayLen : UInt64
  /-- Page-aligned file offset for the overlay's `mmap(2)`. -/
  fileOffset     : UInt64
  /-- Bytes from `filesz` to the overlay's page-aligned end —
      file-mapped (not zero-guaranteed), explicitly zeroed via the
      per-segment `Zero` slot. -/
  partialBssLen  : UInt64
  /-- POSIX `PROT_*` bits derived from gabi `PF_*`. -/
  prot           : UInt32

namespace SegmentPlan

/-- Compute the loader view of a `Segment`. -/
def ofSegment (s : Segment) : SegmentPlan :=
  let ea             := effectiveAlign s.align
  let pageVaddr      := alignDown s.vaddr ea
  let pageEnd        := alignUp (s.vaddr + s.memsz) ea
  let pageLength     := pageEnd - pageVaddr
  let pageInset      := s.vaddr - pageVaddr
  let fileOverlayLen := alignUp (pageInset + s.filesz) ea
  let fileOffset     := alignDown s.offset ea
  let partialBssLen  := fileOverlayLen - (pageInset + s.filesz)
  let prot : UInt32 :=
    (if s.perm.read  then (1 : UInt32) else 0) |||
    (if s.perm.write then (2 : UInt32) else 0) |||
    (if s.perm.exec  then (4 : UInt32) else 0)
  { segment := s, pageVaddr, pageLength, pageInset,
    fileOverlayLen, fileOffset, partialBssLen, prot }

/-- One past the last byte of the mmap'd range, base-relative. -/
def pageEndAddr (sp : SegmentPlan) : UInt64 := sp.pageVaddr + sp.pageLength

/-- True when the segment has any file-backed bytes. -/
def hasFileBacked (sp : SegmentPlan) : Bool := sp.fileOverlayLen > 0

/-- True when there are partial-page BSS bytes to zero. -/
def hasPartialBss (sp : SegmentPlan) : Bool := sp.partialBssLen > 0

end SegmentPlan

/-- Page-aligned segment ranges are sorted: each one's `pageEndAddr`
    is ≤ the next one's `pageVaddr`. Base-free; translation
    invariant. Same shape as `Elaborate.Sorted`, but on the
    page-aligned ranges. -/
def Sorted (segs : Array SegmentPlan) : Prop :=
  ∀ i, ∀ _ : i < segs.size, ∀ j, ∀ _ : j < segs.size,
    i < j → segs[i].pageEndAddr ≤ segs[j].pageVaddr

instance (segs : Array SegmentPlan) : Decidable (Sorted segs) := by
  unfold Sorted; infer_instance

-- ============================================================================
-- ElfPlan — one elf's SegmentPlans + objectSpan + sorted proof.
-- ============================================================================

/-- One elf's segment plans, the contiguous span its segments
    occupy, and a proof that the page-aligned ranges don't overlap.
    Construction (`ofElf`) is fallible: it fails when the validation
    rejects the elf. -/
structure ElfPlan where
  elf            : Elf
  /-- Parallel to `elf.segments`, lifted to the loader view. -/
  segments       : Array SegmentPlan
  /-- Cumulative span: max `pageEndAddr` over `segments`. The
      reservation needs at least `alignUp objectSpan 0x1000` bytes per
      elf. -/
  objectSpan     : UInt64
  /-- Page-aligned segment ranges don't overlap pairwise. -/
  segmentsSorted : Sorted segments

namespace ElfPlan

/-- Build an `ElfPlan`, validating page-aligned non-overlap.
    `Elaborate.Sorted` and `Elaborate.NonOverlap` are on raw vaddrs;
    after page-rounding, small-alignment edge cases can collapse two
    segments onto the same page (modern toolchains never emit this,
    but it's not statically excluded by gabi-level invariants). -/
def ofElf (e : Elf) : Except String ElfPlan :=
  let segs := e.segments.map SegmentPlan.ofSegment
  if h : Sorted segs then
    let objectSpan := segs.foldl (init := 0) fun acc sp =>
      max acc sp.pageEndAddr
    .ok { elf := e, segments := segs, objectSpan, segmentsSorted := h }
  else
    .error "ElfPlan.ofElf: PT_LOAD page-aligned ranges overlap"

end ElfPlan

-- ============================================================================
-- LoadPlan — every elf's plan + the cumulative reservation span.
-- ============================================================================

/-- Top-level base-free plan. `totalSpan` is the `len` to pass to
    `Runtime.mmapAnonAlloc` at the IO boundary. -/
structure LoadPlan where
  elfs      : Array ElfPlan
  /-- `Σ alignUp objectSpan 0x1000` — cumulative reservation span. -/
  totalSpan : UInt64

namespace LoadPlan

/-- Tail-recursive accumulator that lifts each `Elf` through
    `ElfPlan.ofElf` while maintaining `acc.size = i`. -/
private def buildElfPlans (es : Array Elf) (i : Nat) (h : i ≤ es.size)
    (acc : { a : Array ElfPlan // a.size = i }) :
    Except String { a : Array ElfPlan // a.size = es.size } :=
  if heq : i = es.size then
    .ok ⟨acc.val, heq ▸ acc.property⟩
  else
    have hi : i < es.size := Nat.lt_of_le_of_ne h heq
    match ElfPlan.ofElf es[i] with
    | .error e => .error e
    | .ok ep =>
      let acc' : { a : Array ElfPlan // a.size = i + 1 } :=
        ⟨acc.val.push ep, by rw [Array.size_push, acc.property]⟩
      buildElfPlans es (i + 1) hi acc'
termination_by es.size - i

/-- Build the full base-free plan from raw elfs. Each elf goes
    through `ElfPlan.ofElf`, which validates page-aligned
    non-overlap. The result subtype carries `lp.elfs.size = es.size`
    so callers can match `Resolve.Table` and `LoadRelocs` indices. -/
def ofElfs (es : Array Elf) :
    Except String { lp : LoadPlan // lp.elfs.size = es.size } := do
  let elfPlans ← buildElfPlans es 0 (Nat.zero_le _) ⟨#[], by simp⟩
  let totalSpan := elfPlans.val.foldl (init := 0) fun acc ep =>
    acc + alignUp ep.objectSpan 0x1000
  return ⟨{ elfs := elfPlans.val, totalSpan }, elfPlans.property⟩

end LoadPlan

-- ============================================================================
-- Base assignment (IO-supplied `base`). Total: every `LoadPlan`
-- produces a valid bases array.
-- ============================================================================

/-- Stack each elf at `cursor`, advancing by `alignUp objectSpan 0x1000`. -/
def assignBases (base : UInt64) (lp : LoadPlan) : Array UInt64 :=
  let f : (Array UInt64 × UInt64) → ElfPlan → (Array UInt64 × UInt64) :=
    fun (bases, cursor) ep =>
      let advance := alignUp ep.objectSpan 0x1000
      (bases.push cursor, cursor + advance)
  (lp.elfs.foldl (init := (Array.mkEmpty lp.elfs.size, base)) f).fst

theorem assignBases_size (base : UInt64) (lp : LoadPlan) :
    (assignBases base lp).size = lp.elfs.size := by
  unfold assignBases
  let motive : Nat → Array UInt64 × UInt64 → Prop := fun n p => p.fst.size = n
  show motive lp.elfs.size _
  refine Array.foldl_induction motive ?_ ?_
  · show (Array.mkEmpty lp.elfs.size).size = 0; simp
  · intro idx ⟨bases, cursor⟩ ih
    have ih' : bases.size = idx.val := ih
    show (bases.push cursor, cursor + _).fst.size = idx.val + 1
    simp [ih']

end LeanLoad.Plan

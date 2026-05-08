/-
Layout planning — base-free.

Each PT_LOAD `Segment` lifts to a `SegmentPlan` whose page math is
precomputed once and stored: `pageVaddr`, `pageLength`, `pageInset`,
`fileOverlayLen`, `fileOffset`, `partialBssLen`, `prot`. Every offset
is relative to `base = 0`; the materializer adds the chosen base
when emitting `MemoryOp`s.

Hierarchy:
  • `SegmentPlan` — one PT_LOAD with all loader-view fields stored.
  • `ElfPlan`     — one elf's `SegmentPlan`s plus its `objectSpan`.
  • `LoadPlan`    — every elf's `ElfPlan` plus the cumulative
                    `totalSpan` (the `len` for `mmapAnonAlloc`).

`LoadPlan.ofElfs` builds the whole tree in one pass. `assignBases
base lp` takes the IO-supplied reservation start and stacks each elf
by `alignUp objectSpan 0x1000`. `layouts` does the same and
validates `segmentsSorted` per elf.

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
    `MemoryOp`s. -/
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
      file-mapped (not zero-guaranteed), explicitly zeroed via
      `zeroout`. -/
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
    invariant. -/
def segmentsSorted (segs : Array SegmentPlan) : Prop :=
  ∀ i, ∀ _ : i < segs.size, ∀ j, ∀ _ : j < segs.size,
    i < j → segs[i].pageEndAddr ≤ segs[j].pageVaddr

instance (segs : Array SegmentPlan) : Decidable (segmentsSorted segs) := by
  unfold segmentsSorted; infer_instance

-- ============================================================================
-- ElfPlan — one elf's SegmentPlans + objectSpan.
-- ============================================================================

/-- One elf's segment plans + the contiguous span its segments
    occupy. Base-free. -/
structure ElfPlan where
  elf        : Elf
  /-- Parallel to `elf.segments`, lifted to the loader view. -/
  segments   : Array SegmentPlan
  /-- Cumulative span: max `pageEndAddr` over `segments`. The
      reservation needs at least `alignUp objectSpan 0x1000` bytes per
      elf. -/
  objectSpan : UInt64

namespace ElfPlan

def ofElf (e : Elf) : ElfPlan :=
  let segments := e.segments.map SegmentPlan.ofSegment
  let objectSpan := segments.foldl (init := 0) fun acc sp =>
    max acc sp.pageEndAddr
  { elf := e, segments, objectSpan }

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

/-- Build the full base-free plan from raw elfs. -/
def ofElfs (es : Array Elf) : LoadPlan :=
  let elfs := es.map ElfPlan.ofElf
  let totalSpan := elfs.foldl (init := 0) fun acc ep =>
    acc + alignUp ep.objectSpan 0x1000
  { elfs, totalSpan }

theorem ofElfs_size (es : Array Elf) : (ofElfs es).elfs.size = es.size := by
  simp [ofElfs]

end LoadPlan

-- ============================================================================
-- Base assignment (IO-supplied `base`). The reservation start comes
-- from `Runtime.mmapAnonAlloc` (kernel-picked) or, in tests, any
-- synthetic UInt64.
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

/-- Build the per-elf bases and validate `segmentsSorted` per elf.
    Production threads `base` from `Runtime.mmapAnonAlloc`. -/
def layouts (base : UInt64) (lp : LoadPlan) :
    Except String { bases : Array UInt64 //
      bases.size = lp.elfs.size ∧
      ∀ (i : Nat) (h : i < lp.elfs.size),
        segmentsSorted lp.elfs[i].segments } :=
  let bases := assignBases base lp
  have hBases : bases.size = lp.elfs.size := assignBases_size base lp
  match harr : lp.elfs.findIdx? (fun ep => ¬ segmentsSorted ep.segments) with
  | some i =>
    .error s!"layouts: object[{i}] has malformed PT_LOAD segments"
  | none =>
    .ok ⟨bases, hBases, by
      intro i hi
      have hall : ∀ x ∈ lp.elfs, decide (¬ segmentsSorted x.segments) = false :=
        Array.findIdx?_eq_none_iff.mp harr
      have hi_in : lp.elfs[i] ∈ lp.elfs := Array.getElem_mem hi
      have := hall lp.elfs[i] hi_in
      simp at this
      exact this⟩

end LeanLoad.Plan

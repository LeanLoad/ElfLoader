/-
Layout — per-object segment arrangement, pure.

Spec: gabi 07 § Program Header (positional concerns — base
assignment, span over loadable segments).

Layout consumes `Array Parse.Segment.Segment` (typed `PT_LOAD`s)
that the parser already produced, and assigns each object an mmap
base + builds the per-object plan that Map / Reloc / Apply / Exec
consume. Validation that the parser-produced segments are page-
aligned-sorted and non-overlapping happens at the boundary in
`g.layouts`, which returns a sized subtype carrying the witness.

Init/fini ordering lives in `LeanLoad.Plan.Init` (gabi 08); this
file is purely gabi-07.
-/

import LeanLoad.Parse.Segment
import LeanLoad.Plan.Discover
import LeanLoad.Spec.Program

namespace LeanLoad.Layout

open LeanLoad
open LeanLoad.Spec
open LeanLoad.Spec.Program (Segment)
open LeanLoad.Discover
open LeanLoad.Parse.Segment

-- ============================================================================
-- PF_* → PROT_* translation (loader-level: gabi `PF_*` → POSIX `PROT_*`)
-- ============================================================================

/-- Translate program-header permissions (gabi 07 § Segment Permissions)
    to the corresponding `PROT_*` bits for `mprotect`. The bit
    positions are swapped between PF_* and PROT_*: `PF_X=1, PF_W=2,
    PF_R=4` vs `PROT_READ=1, PROT_WRITE=2, PROT_EXEC=4`, so each
    flag must be translated explicitly. `PROT_*` is POSIX, not gabi —
    this is loader-level. -/
def protOfFlags (pflags : UInt32) : UInt32 :=
  let r := if (pflags &&& Program.PF_R) != 0 then (1 : UInt32) else 0
  let w := if (pflags &&& Program.PF_W) != 0 then (2 : UInt32) else 0
  let x := if (pflags &&& Program.PF_X) != 0 then (4 : UInt32) else 0
  r ||| w ||| x

#guard protOfFlags (Program.PF_R ||| Program.PF_X) = 5
#guard protOfFlags (Program.PF_R ||| Program.PF_W) = 3
#guard protOfFlags Program.PF_R = 1
#guard protOfFlags (Program.PF_R + Program.PF_X) = 5

-- ============================================================================
-- Page alignment helpers (loader-level: required by mmap(2))
-- ============================================================================

/-- Round `x` down to a multiple of `align`. `align` must be a power of two
    (or zero, treated as 1). -/
def alignDown (x align : UInt64) : UInt64 :=
  if align == 0 then x else x - (x % align)

/-- Round `x` up to a multiple of `align`. -/
def alignUp (x align : UInt64) : UInt64 :=
  if align == 0 then x else alignDown (x + align - 1) align

#guard alignDown 0x1234 0x1000 == 0x1000
#guard alignUp 0x1234 0x1000 == 0x2000
#guard alignDown 0x1000 0x1000 == 0x1000
#guard alignUp   0x1000 0x1000 == 0x1000
#guard alignDown 0x1234 0 == 0x1234
#guard alignUp   0x1234 0 == 0x1234

end LeanLoad.Layout

-- ============================================================================
-- Loader-level views of a `Segment` — page-aligned mmap addresses,
-- POSIX `PROT_*` translation. Defined under the `Parse.Segment.Segment`
-- namespace so dot notation works (`s.vaddr`, `s.length`, …) wherever
-- this file is imported. The parse-level type stays minimal; these
-- are extension methods.
-- ============================================================================

namespace LeanLoad.Spec.Program.Segment

open LeanLoad.Layout
open LeanLoad.Spec.Program

/-- Effective alignment (treats `p_align = 0` as 1). -/
private def effectiveAlign (s : Segment) : UInt64 :=
  if s.phdr.p_align == 0 then 1 else s.phdr.p_align

/-- Page-aligned mmap base. -/
def vaddr (s : Segment) : UInt64 := alignDown s.phdr.p_vaddr s.effectiveAlign

/-- mmap length in bytes (page-aligned over the full memory range). -/
def length (s : Segment) : UInt64 :=
  alignUp (s.phdr.p_vaddr + s.phdr.p_memsz) s.effectiveAlign - s.vaddr

/-- POSIX `PROT_*` bits for `mprotect`, translated from gabi `PF_*`. -/
def prot (s : Segment) : UInt32 := protOfFlags s.phdr.p_flags

/-- Offset within the mapped region where copied bytes begin (handles
    the case `p_vaddr` is not page-aligned). -/
def pageInset (s : Segment) : UInt64 := s.phdr.p_vaddr - s.vaddr

/-- Page-aligned length of the file-backed mmap range: covers
    `pageInset + fileLen` rounded up. `≤ length` (BSS tail extends
    beyond). -/
def fileLenPaged (s : Segment) : UInt64 :=
  alignUp (s.pageInset + s.fileLen) s.effectiveAlign

/-- Page-aligned file offset for `mmap(2)`. Equals `p_offset -
    pageInset` for gabi-07-conforming ELFs (the congruence
    `p_vaddr ≡ p_offset (mod p_align)`). -/
def fileOffsetPaged (s : Segment) : UInt64 :=
  alignDown s.phdr.p_offset s.effectiveAlign

/-- One past the last byte of the segment's mmap'd range. -/
def endAddr (s : Segment) : UInt64 := s.vaddr + s.length

/-- Two segments are disjoint when their `[vaddr, endAddr)` ranges don't overlap. -/
def disjoint (s₁ s₂ : Segment) : Prop :=
  s₁.endAddr ≤ s₂.vaddr ∨ s₂.endAddr ≤ s₁.vaddr

end LeanLoad.Spec.Program.Segment

namespace LeanLoad.Layout

open LeanLoad
open LeanLoad.Spec
open LeanLoad.Spec.Program (Segment)
open LeanLoad.Discover
open LeanLoad.Parse.Segment

-- Page-aligned vaddr at 0x1000, fits in one 0x1000 page → no inset.
#guard
  let s : Segment := ⟨{ (default : Program.Header64) with
    p_type := Program.PT_LOAD,
    p_vaddr := 0x1000, p_memsz := 0x800, p_filesz := 0x800,
    p_align := 0x1000, p_flags := Program.PF_R ||| Program.PF_X,
    p_offset := 0x1000 }, by decide⟩
  s.vaddr = 0x1000 ∧ s.length = 0x1000 ∧ s.pageInset = 0 ∧ s.prot = 5
-- Unaligned vaddr 0x1234 with 0x1000 alignment.
#guard
  let s : Segment := ⟨{ (default : Program.Header64) with
    p_type := Program.PT_LOAD,
    p_vaddr := 0x1234, p_memsz := 0x100, p_filesz := 0x100,
    p_align := 0x1000, p_flags := Program.PF_R ||| Program.PF_W,
    p_offset := 0x1234 }, by decide⟩
  s.vaddr = 0x1000 ∧ s.length = 0x1000 ∧ s.pageInset = 0x234 ∧ s.prot = 3
-- p_align = 0 ⇒ identity.
#guard
  let s : Segment := ⟨{ (default : Program.Header64) with
    p_type := Program.PT_LOAD,
    p_vaddr := 0x42, p_memsz := 0x10, p_filesz := 0x10,
    p_align := 0, p_flags := Program.PF_R }, by decide⟩
  s.vaddr = 0x42 ∧ s.length = 0x10 ∧ s.pageInset = 0
-- BSS tail: memsz > filesz.
#guard
  let s : Segment := ⟨{ (default : Program.Header64) with
    p_type := Program.PT_LOAD,
    p_vaddr := 0x2000, p_memsz := 0x800, p_filesz := 0x200,
    p_align := 0x1000, p_flags := Program.PF_R ||| Program.PF_W,
    p_offset := 0x2000 }, by decide⟩
  s.fileLen = 0x200 ∧ s.length = 0x1000

-- ============================================================================
-- ObjectLayout — per-object plan with chosen base.
-- ============================================================================

/-- Layout for a single loaded object.

    `base` is the absolute mmap address at which the object's
    segments will be placed. For `ET_EXEC` (vaddrs already absolute)
    `base = 0` and Map uses `s.vaddr` directly. For `ET_DYN`, Layout
    picks `base = dynAnchor + cumulative_offset` so each object lives
    in its own non-overlapping slot starting at `dynAnchor`; Map then
    uses `MAP_FIXED` everywhere — no kernel-chosen bases.

    There's no `objectIdx` field — a layout is identified by its
    position in the parent array (`g.layouts.val[i]` corresponds to
    `g.objects[i]`), so storing the index would be redundant state. -/
structure ObjectLayout where
  /-- Absolute mmap base address chosen by Layout. -/
  base      : UInt64
  segments  : Array Segment
  /-- The `e_entry` field. `none` for objects we never enter
      (e.g. shared libraries). -/
  entry     : Option UInt64
  /-- True for the main executable. -/
  isMain    : Bool
  deriving Repr

/-- Hardcoded anchor for the first `ET_DYN` object. Subsequent
    `ET_DYN` objects stack above it. Picked to be high enough to
    avoid colliding with the host process's typical mappings on
    x86-64 / aarch64 (heap, libc, etc., usually in the low GB). -/
def dynAnchor : UInt64 := 0x80000000

/-- The contiguous span an array of segments needs (relative to the
    object's base). Used by `assignBases` (with `segmentsOf elf`) to
    size each `ET_DYN` object's arena slot, and by `Map` (with
    `lyt.segments`) for the per-object anon reservation. -/
def objectSpan (segments : Array Segment) : UInt64 :=
  segments.foldl (init := 0) fun acc s => max acc s.endAddr

/-- The contiguous span of one object's segments — convenience
    accessor for `objectSpan lyt.segments`, enables `lyt.span`. -/
def ObjectLayout.span (lyt : ObjectLayout) : UInt64 :=
  objectSpan lyt.segments

/-- Layout for a single parsed ELF. `base` is decided by the
    enclosing `ObjectList.layouts` (anchor + cumulative for `ET_DYN`,
    0 for `ET_EXEC`). -/
def objectLayout (isMain : Bool) (base : UInt64)
    (elf : Parse.File.ParsedElf) : ObjectLayout :=
  let entry := if isMain then some elf.header.e_entry else none
  { base, segments := Parse.File.segmentsOf elf, entry, isMain }

/-- Segments are pairwise disjoint (`[vaddr, endAddr)` ranges don't overlap). -/
def ObjectLayout.segmentsPairwiseDisjoint (lyt : ObjectLayout) : Prop :=
  ∀ i j (_ : i < lyt.segments.size) (_ : j < lyt.segments.size),
    i ≠ j → Segment.disjoint lyt.segments[i] lyt.segments[j]

/-- Segments are sorted by `vaddr` with each one's end ≤ the next one's start.
    The clean precondition under which pairwise disjointness follows. The
    real-ELF discharge comes from `segmentsSortedB` — a decidable Bool
    mirror checked at runtime in `ObjectList.layouts`, with the forward
    bridge `segmentsSorted_of_segmentsSortedB` below. -/
def ObjectLayout.segmentsSorted (lyt : ObjectLayout) : Prop :=
  ∀ i j (_ : i < lyt.segments.size) (_ : j < lyt.segments.size),
    i < j → lyt.segments[i].endAddr ≤ lyt.segments[j].vaddr

/-- Decidable Bool mirror of `segmentsSorted` over loader-level
    page-aligned `vaddr`/`endAddr`. The O(n²) pairwise scan is fine —
    real ELFs have <10 PT_LOAD entries. -/
def ObjectLayout.segmentsSortedB (lyt : ObjectLayout) : Bool :=
  (List.range lyt.segments.size).all fun i =>
    (List.range lyt.segments.size).all fun j =>
      !decide (i < j) ||
        (match lyt.segments[i]?, lyt.segments[j]? with
         | some s, some s' => decide (s.endAddr ≤ s'.vaddr)
         | _, _ => true)

/-- Forward bridge: the runtime check decides the proof-level invariant.
    Used inline by `ObjectList.layouts` to discharge the per-layout
    sortedness obligation in its return subtype. The converse and full
    iff statement live in `Thm/Layout.lean`. -/
theorem ObjectLayout.segmentsSorted_of_segmentsSortedB
    (lyt : ObjectLayout) (h : lyt.segmentsSortedB = true) :
    lyt.segmentsSorted := by
  intro i j hi hj hlt
  unfold ObjectLayout.segmentsSortedB at h
  rw [List.all_eq_true] at h
  have h1 := h i (List.mem_range.mpr hi)
  rw [List.all_eq_true] at h1
  have h2 := h1 j (List.mem_range.mpr hj)
  rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hj] at h2
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
             decide_eq_false_iff_not, decide_eq_true_eq] at h2
  rcases h2 with hnlt | hle
  · exact absurd hlt hnlt
  · exact hle

-- ============================================================================
-- Layout-stage output is `Array ObjectLayout` (one entry per object,
-- in `ObjectList.objects` order). `g.layouts` returns
-- `Except String (Array ObjectLayout)` — the well-formedness check
-- runs here at the boundary; a malformed ELF surfaces as an error
-- before Map (which would otherwise produce undefined behaviour
-- against `MAP_FIXED`).
--
-- Init/fini order (gabi 08) is computed separately in `LeanLoad.Order`
-- and threaded directly to `Exec.runInits` — purely gabi-07 here
-- (segment placement). Relocations are not part of `Layout` either;
-- they depend on actual chosen bases and are computed post-Map by
-- `LeanLoad.Reloc.plan`.
-- ============================================================================

/-- Assign an mmap base to each object in BFS order. `ET_EXEC`
    objects keep `0`; `ET_DYN` objects start at `dynAnchor` and
    stack by `alignUp objectSpan 0x1000`. -/
def assignBases (g : ObjectList) : Array UInt64 := Id.run do
  let mut bases : Array UInt64 := Array.mkEmpty g.val.size
  let mut cursor : UInt64 := dynAnchor
  for h : i in [:g.val.size] do
    let obj := g.val[i]
    let isExec := obj.elf.header.e_type = 2
    let base := if isExec then 0 else cursor
    bases := bases.push base
    if !isExec then
      cursor := cursor + alignUp (objectSpan (Parse.File.segmentsOf obj.elf)) 0x1000
  return bases

section Example
open LeanLoad.Spec.Header (ET_EXEC ET_DYN)

/-- Synthetic `LoadedObject` with the given `e_type`, no PT_LOAD
    segments. Empty phdrs means `objectSpan = 0`, so the cursor
    doesn't actually advance between consecutive ET_DYN entries —
    the cumulative-stacking aspect of `assignBases` is exercised
    E2E (run.sh against `build/main`). What this Example exercises
    is the per-entry *dispatch*: ET_EXEC ⇒ 0, ET_DYN ⇒ cursor. -/
private def synthEt (name : String) (etype : UInt16) : Discover.LoadedObject :=
  let hdr : Spec.Header.ElfHeader64 :=
    { (default : Spec.Header.ElfHeader64) with e_type := etype }
  let elf : Parse.File.ParsedElf :=
    { (default : Parse.File.ParsedElf) with phdrs := #[], header := hdr }
  { name, path := s!"<synth:{name}>", handle := none, elf,
    elf_wf := Parse.Segment.WellFormed_nil }

private def synthList (objs : Array Discover.LoadedObject) (h : 0 < objs.size) :
    Discover.ObjectList := ⟨objs, h⟩

-- Single ET_EXEC main → base = 0.
#guard assignBases (synthList #[synthEt "main" ET_EXEC] (by simp)) = #[0]

-- Single ET_DYN object → base = dynAnchor (0x80000000).
#guard assignBases (synthList #[synthEt "lib" ET_DYN] (by simp)) = #[dynAnchor]

-- Mixed: ET_EXEC main + two ET_DYN libs. With empty phdrs all
-- objectSpans are 0, so all ET_DYNs share the same dynAnchor base
-- (real linkers produce non-empty PT_LOADs whose spans drive the
-- cumulative cursor; that path is E2E-tested).
#guard assignBases (synthList #[synthEt "main" ET_EXEC,
                                 synthEt "libfoo" ET_DYN,
                                 synthEt "libbar" ET_DYN] (by simp))
       = #[0, dynAnchor, dynAnchor]
end Example

end LeanLoad.Layout

namespace LeanLoad.Discover.ObjectList

open LeanLoad.Layout
open LeanLoad.Parse.Segment

/-- Build the per-object layouts for a discovered dep graph. The
    first object (index 0) is main. Each layout's segments are checked
    for loader-level well-formedness (page-aligned `[vaddr, endAddr)`
    ranges sorted and non-overlapping — required for `MAP_FIXED`
    correctness). A malformed object surfaces as `error`.

    Returns a sized subtype carrying *two* invariants in the type:

    - `a.size = g.objects.size` — one layout per object, by construction.
    - `∀ i, a[i].segmentsSorted` — per-layout sortedness, which combined
      with `Thm.segmentsPairwiseDisjoint_of_segmentsSorted` discharges
      `segmentsPairwiseDisjoint` for every layout.

    Downstream consumers (`Map.mapAll`, `Reloc.plan`) get both for free
    without runtime checks. -/
def layouts (g : ObjectList) :
    Except String { a : Array ObjectLayout //
      a.size = g.val.size ∧
      ∀ (i : Nat) (h : i < a.size), a[i].segmentsSorted } :=
  let bases := assignBases g
  let arr := g.val.mapIdx fun i obj =>
    objectLayout (i = 0) (bases[i]?.getD 0) obj.elf
  match harr : arr.findIdx? (fun lyt => lyt.segmentsSortedB == false) with
  | some i =>
    let name := (g.val[i]?.map (·.name)).getD "?"
    .error s!"layouts: object[{i}] ({name}) has malformed PT_LOAD segments"
  | none =>
    .ok ⟨arr, by
      refine ⟨by simp [arr], ?_⟩
      intro i hi
      have hall : ∀ x ∈ arr, (x.segmentsSortedB == false) = false :=
        Array.findIdx?_eq_none_iff.mp harr
      have hi_in : arr[i] ∈ arr := Array.getElem_mem hi
      have hb : arr[i].segmentsSortedB = true := by
        have := hall arr[i] hi_in
        simp at this
        exact this
      exact ObjectLayout.segmentsSorted_of_segmentsSortedB _ hb⟩

end LeanLoad.Discover.ObjectList

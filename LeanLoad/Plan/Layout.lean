/-
Layout — per-object segment arrangement, pure.

Spec: gabi 07 § Program Header (positional concerns — base
assignment, span over loadable segments).

Layout consumes the elaborated PT_LOAD phdrs from
`obj.elf.loadablePhdrs` and assigns each object an mmap base + builds
the per-object plan that Reloc / Apply / Exec consume. Validation
that the page-aligned segments are sorted and non-overlapping happens
at the boundary in `g.layouts`, which returns a sized subtype carrying
the witness.

Init/fini ordering lives in `LeanLoad.Plan.Init` (gabi 08); this
file is purely gabi-07.
-/

import LeanLoad.Elaborate.Segment
import LeanLoad.Elaborate.Elf
import LeanLoad.Plan.Discover
import LeanLoad.Parse.Structs

namespace LeanLoad.Layout

open LeanLoad
open LeanLoad.Parse
open LeanLoad.Elaborate (Prot)
open LeanLoad.Discover

-- ============================================================================
-- Prot → PROT_* translation (loader-level: typed `Prot` → POSIX `PROT_*`)
-- ============================================================================

/-- Translate typed segment permissions to POSIX `PROT_*` bits for
    `mprotect`. -/
def protOfPerm (p : Prot) : UInt32 :=
  (if p.read  then (1 : UInt32) else 0) |||
  (if p.write then (2 : UInt32) else 0) |||
  (if p.exec  then (4 : UInt32) else 0)

#guard protOfPerm { read := true,  write := false, exec := true  } = 5
#guard protOfPerm { read := true,  write := true,  exec := false } = 3
#guard protOfPerm { read := true,  write := false, exec := false } = 1

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
-- POSIX `PROT_*` translation. Defined under `Elaborate.Segment`'s
-- namespace so dot notation works (`s.pageVaddr`, `s.pageLength`, …).
-- These are loader decisions (mmap concerns), not gabi-mandated.
-- ============================================================================

namespace LeanLoad.Elaborate.Segment

open LeanLoad.Layout

/-- Effective alignment (treats `align = 0` as 1). -/
def effectiveAlign (s : Segment) : UInt64 :=
  if s.align == 0 then 1 else s.align

/-- Page-aligned mmap base. -/
def pageVaddr (s : Segment) : UInt64 := alignDown s.vaddr s.effectiveAlign

/-- mmap length in bytes (page-aligned over the full memory range). -/
def pageLength (s : Segment) : UInt64 :=
  alignUp (s.vaddr + s.memsz) s.effectiveAlign - s.pageVaddr

/-- POSIX `PROT_*` bits for `mprotect`, translated from typed `Prot`. -/
def prot (s : Segment) : UInt32 := protOfPerm s.perm

/-- Offset within the mapped region where copied bytes begin (handles
    the case `vaddr` is not page-aligned). -/
def pageInset (s : Segment) : UInt64 := s.vaddr - s.pageVaddr

/-- Page-aligned length of the file-backed mmap range: covers
    `pageInset + filesz` rounded up. `≤ pageLength`. -/
def fileLenPaged (s : Segment) : UInt64 :=
  alignUp (s.pageInset + s.filesz) s.effectiveAlign

/-- Page-aligned file offset for `mmap(2)`. -/
def fileOffsetPaged (s : Segment) : UInt64 :=
  alignDown s.offset s.effectiveAlign

/-- One past the last byte of the segment's mmap'd range. -/
def pageEndAddr (s : Segment) : UInt64 := s.pageVaddr + s.pageLength

/-- Two segments are disjoint when their `[pageVaddr, pageEndAddr)`
    ranges don't overlap. -/
def disjoint (s₁ s₂ : Segment) : Prop :=
  s₁.pageEndAddr ≤ s₂.pageVaddr ∨ s₂.pageEndAddr ≤ s₁.pageVaddr

end LeanLoad.Elaborate.Segment

namespace LeanLoad.Layout

open LeanLoad
open LeanLoad.Parse
open LeanLoad.Elaborate (PF_R PF_W PF_X)
open LeanLoad.Discover

-- Loader-view smoke tests are dropped here — the typed `Segment`
-- requires per-segment witnesses to construct, which makes inline
-- `RawPhdr`-style fixtures unwieldy. End-to-end coverage in `lake test`.

-- ============================================================================
-- ObjectLayout — per-object plan with chosen base.
-- ============================================================================

/-- Layout for a single loaded object.

    `base` is the absolute mmap address at which the object's
    segments will be placed. For `ET_EXEC` (vaddrs already absolute)
    `base = 0`. For `ET_DYN`, Layout picks `base = dynAnchor +
    cumulative_offset` so each object lives in its own non-overlapping
    slot starting at `dynAnchor`. -/
structure ObjectLayout where
  /-- Absolute mmap base address chosen by Layout. -/
  base      : UInt64
  segments  : Array Elaborate.Segment
  /-- The `e_entry` field. `none` for objects we never enter. -/
  entry     : Option UInt64
  /-- True for the main executable. -/
  isMain    : Bool

/-- Hardcoded anchor for the first `ET_DYN` object. Picked to avoid
    colliding with the host process's typical mappings on x86-64 /
    aarch64 (heap, libc, etc., usually in the low GB). -/
def dynAnchor : UInt64 := 0x80000000

/-- The contiguous span an array of segments needs (relative to the
    object's base). -/
def objectSpan (segments : Array Elaborate.Segment) : UInt64 :=
  segments.foldl (init := 0) fun acc s => max acc s.pageEndAddr

/-- The contiguous span of one object's segments. -/
def ObjectLayout.span (lyt : ObjectLayout) : UInt64 :=
  objectSpan lyt.segments

/-- Layout for a single elaborated ELF. -/
def objectLayout (isMain : Bool) (base : UInt64) (elf : Elaborate.Elf) : ObjectLayout :=
  let entry := if isMain then some elf.entry else none
  { base, segments := elf.segments, entry, isMain }

/-- Segments are pairwise disjoint. -/
def ObjectLayout.segmentsPairwiseDisjoint (lyt : ObjectLayout) : Prop :=
  ∀ i j (_ : i < lyt.segments.size) (_ : j < lyt.segments.size),
    i ≠ j → Elaborate.Segment.disjoint lyt.segments[i] lyt.segments[j]

/-- Segments are sorted by page-aligned vaddr with each one's end ≤
    the next one's start. Bounded ∀ so Lean derives `Decidable`
    automatically. -/
def ObjectLayout.segmentsSorted (lyt : ObjectLayout) : Prop :=
  ∀ i, ∀ _ : i < lyt.segments.size, ∀ j, ∀ _ : j < lyt.segments.size,
    i < j → lyt.segments[i].pageEndAddr ≤ lyt.segments[j].pageVaddr

instance (lyt : ObjectLayout) : Decidable lyt.segmentsSorted := by
  unfold ObjectLayout.segmentsSorted; infer_instance

/-- Decidable Bool mirror of `segmentsSorted`. -/
def ObjectLayout.segmentsSortedB (lyt : ObjectLayout) : Bool :=
  decide lyt.segmentsSorted

/-- Forward bridge: the runtime check decides the proof-level invariant. -/
theorem ObjectLayout.segmentsSorted_of_segmentsSortedB
    (lyt : ObjectLayout) (h : lyt.segmentsSortedB = true) :
    lyt.segmentsSorted := of_decide_eq_true h

-- ============================================================================
-- Layout-stage entry point.
-- ============================================================================

/-- Assign an mmap base to each object in BFS order. `.exec`
    objects keep `0`; `.dyn` (and others) start at `dynAnchor` and
    stack by `alignUp objectSpan 0x1000`. -/
def assignBases (g : ObjectList) : Array UInt64 :=
  let f : (Array UInt64 × UInt64) → LoadedObject → (Array UInt64 × UInt64) :=
    fun (bases, cursor) obj =>
      if obj.elf.elfType == .exec then
        (bases.push 0, cursor)
      else
        let advance := alignUp (objectSpan obj.elf.segments) 0x1000
        (bases.push cursor, cursor + advance)
  (g.val.foldl (init := (Array.mkEmpty g.val.size, dynAnchor)) f).fst

section Example
private def synthEt (name : String) (et : Elaborate.ElfType) : Discover.LoadedObject :=
  let elf : Elaborate.Elf := { (default : Elaborate.Elf) with elfType := et }
  { name, path := s!"<synth:{name}>", handle := none, elf }

private def synthList (objs : Array Discover.LoadedObject) (h : 0 < objs.size) :
    Discover.ObjectList := ⟨objs, h⟩

#guard assignBases (synthList #[synthEt "main" .exec] (by simp)) = #[0]
#guard assignBases (synthList #[synthEt "lib" .dyn] (by simp)) = #[dynAnchor]
#guard assignBases (synthList #[synthEt "main" .exec,
                                 synthEt "libfoo" .dyn,
                                 synthEt "libbar" .dyn] (by simp))
       = #[0, dynAnchor, dynAnchor]
end Example

end LeanLoad.Layout

namespace LeanLoad.Discover.ObjectList

open LeanLoad.Layout

/-- Build the per-object layouts for a discovered dep graph. -/
def layouts (g : ObjectList) :
    Except String { a : Array ObjectLayout //
      a.size = g.val.size ∧
      ∀ (i : Nat) (h : i < a.size), a[i].segmentsSorted } :=
  let bases := assignBases g
  let arr := g.val.mapIdx fun i obj =>
    objectLayout (i == 0) (bases[i]?.getD 0) obj.elf
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

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
import LeanLoad.Elaborate.File
import LeanLoad.Plan.Discover
import LeanLoad.Parse.Program

namespace LeanLoad.Layout

open LeanLoad
open LeanLoad.Parse
open LeanLoad.Discover

-- ============================================================================
-- PF_* → PROT_* translation (loader-level: gabi `PF_*` → POSIX `PROT_*`)
-- ============================================================================

/-- Translate program-header permissions (gabi 07 § Segment Permissions)
    to the corresponding `PROT_*` bits for `mprotect`. -/
def protOfFlags (pflags : UInt32) : UInt32 :=
  let r := if (pflags &&& PF_R) != 0 then (1 : UInt32) else 0
  let w := if (pflags &&& PF_W) != 0 then (2 : UInt32) else 0
  let x := if (pflags &&& PF_X) != 0 then (4 : UInt32) else 0
  r ||| w ||| x

#guard protOfFlags (PF_R ||| PF_X) = 5
#guard protOfFlags (PF_R ||| PF_W) = 3
#guard protOfFlags PF_R = 1
#guard protOfFlags (PF_R + PF_X) = 5

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
-- Loader-level views of a `RawPhdr` — page-aligned mmap addresses,
-- POSIX `PROT_*` translation. Defined under the `Parse.RawPhdr`
-- namespace so dot notation works (`s.vaddr`, `s.length`, …).
-- These are loader decisions (mmap concerns), not gabi-mandated.
-- ============================================================================

namespace LeanLoad.Parse.RawPhdr

open LeanLoad.Layout

/-- Effective alignment (treats `p_align = 0` as 1). -/
private def effectiveAlign (s : RawPhdr) : UInt64 :=
  if s.p_align == 0 then 1 else s.p_align

/-- Page-aligned mmap base. -/
def vaddr (s : RawPhdr) : UInt64 := alignDown s.p_vaddr s.effectiveAlign

/-- mmap length in bytes (page-aligned over the full memory range). -/
def length (s : RawPhdr) : UInt64 :=
  alignUp (s.p_vaddr + s.p_memsz) s.effectiveAlign - s.vaddr

/-- POSIX `PROT_*` bits for `mprotect`, translated from gabi `PF_*`. -/
def prot (s : RawPhdr) : UInt32 := protOfFlags s.p_flags

/-- Offset within the mapped region where copied bytes begin (handles
    the case `p_vaddr` is not page-aligned). -/
def pageInset (s : RawPhdr) : UInt64 := s.p_vaddr - s.vaddr

/-- Number of bytes to copy from the file (the `[p_filesz, p_memsz)`
    tail is BSS). -/
def fileLen (s : RawPhdr) : UInt64 := s.p_filesz

/-- Page-aligned length of the file-backed mmap range: covers
    `pageInset + fileLen` rounded up. `≤ length`. -/
def fileLenPaged (s : RawPhdr) : UInt64 :=
  alignUp (s.pageInset + s.fileLen) s.effectiveAlign

/-- Page-aligned file offset for `mmap(2)`. -/
def fileOffsetPaged (s : RawPhdr) : UInt64 :=
  alignDown s.p_offset s.effectiveAlign

/-- One past the last byte of the segment's mmap'd range. -/
def endAddr (s : RawPhdr) : UInt64 := s.vaddr + s.length

/-- Two segments are disjoint when their `[vaddr, endAddr)` ranges don't overlap. -/
def disjoint (s₁ s₂ : RawPhdr) : Prop :=
  s₁.endAddr ≤ s₂.vaddr ∨ s₂.endAddr ≤ s₁.vaddr

end LeanLoad.Parse.RawPhdr

namespace LeanLoad.Layout

open LeanLoad
open LeanLoad.Parse
open LeanLoad.Discover

-- Page-aligned vaddr at 0x1000, fits in one 0x1000 page → no inset.
#guard
  let s : RawPhdr := { (default : RawPhdr) with
    p_type := PT_LOAD,
    p_vaddr := 0x1000, p_memsz := 0x800, p_filesz := 0x800,
    p_align := 0x1000, p_flags := PF_R ||| PF_X,
    p_offset := 0x1000 }
  s.vaddr = 0x1000 ∧ s.length = 0x1000 ∧ s.pageInset = 0 ∧ s.prot = 5
-- Unaligned vaddr 0x1234 with 0x1000 alignment.
#guard
  let s : RawPhdr := { (default : RawPhdr) with
    p_type := PT_LOAD,
    p_vaddr := 0x1234, p_memsz := 0x100, p_filesz := 0x100,
    p_align := 0x1000, p_flags := PF_R ||| PF_W,
    p_offset := 0x1234 }
  s.vaddr = 0x1000 ∧ s.length = 0x1000 ∧ s.pageInset = 0x234 ∧ s.prot = 3
-- p_align = 0 ⇒ identity.
#guard
  let s : RawPhdr := { (default : RawPhdr) with
    p_type := PT_LOAD,
    p_vaddr := 0x42, p_memsz := 0x10, p_filesz := 0x10,
    p_align := 0, p_flags := PF_R }
  s.vaddr = 0x42 ∧ s.length = 0x10 ∧ s.pageInset = 0
-- BSS tail: memsz > filesz.
#guard
  let s : RawPhdr := { (default : RawPhdr) with
    p_type := PT_LOAD,
    p_vaddr := 0x2000, p_memsz := 0x800, p_filesz := 0x200,
    p_align := 0x1000, p_flags := PF_R ||| PF_W,
    p_offset := 0x2000 }
  s.fileLen = 0x200 ∧ s.length = 0x1000

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
  segments  : Array RawPhdr
  /-- The `e_entry` field. `none` for objects we never enter. -/
  entry     : Option UInt64
  /-- True for the main executable. -/
  isMain    : Bool
  deriving Repr

/-- Hardcoded anchor for the first `ET_DYN` object. Picked to avoid
    colliding with the host process's typical mappings on x86-64 /
    aarch64 (heap, libc, etc., usually in the low GB). -/
def dynAnchor : UInt64 := 0x80000000

/-- The contiguous span an array of segments needs (relative to the
    object's base). -/
def objectSpan (segments : Array RawPhdr) : UInt64 :=
  segments.foldl (init := 0) fun acc s => max acc s.endAddr

/-- The contiguous span of one object's segments. -/
def ObjectLayout.span (lyt : ObjectLayout) : UInt64 :=
  objectSpan lyt.segments

/-- Layout for a single elaborated ELF. -/
def objectLayout (isMain : Bool) (base : UInt64) (elf : Elaborate.Elf) : ObjectLayout :=
  let entry := if isMain then some elf.header.e_entry else none
  { base, segments := elf.loadablePhdrs, entry, isMain }

/-- Segments are pairwise disjoint. -/
def ObjectLayout.segmentsPairwiseDisjoint (lyt : ObjectLayout) : Prop :=
  ∀ i j (_ : i < lyt.segments.size) (_ : j < lyt.segments.size),
    i ≠ j → RawPhdr.disjoint lyt.segments[i] lyt.segments[j]

/-- Segments are sorted by `vaddr` with each one's end ≤ the next
    one's start. -/
def ObjectLayout.segmentsSorted (lyt : ObjectLayout) : Prop :=
  ∀ i j (_ : i < lyt.segments.size) (_ : j < lyt.segments.size),
    i < j → lyt.segments[i].endAddr ≤ lyt.segments[j].vaddr

/-- Decidable Bool mirror of `segmentsSorted` over loader-level
    page-aligned `vaddr`/`endAddr`. -/
def ObjectLayout.segmentsSortedB (lyt : ObjectLayout) : Bool :=
  (List.range lyt.segments.size).all fun i =>
    (List.range lyt.segments.size).all fun j =>
      !decide (i < j) ||
        (match lyt.segments[i]?, lyt.segments[j]? with
         | some s, some s' => decide (s.endAddr ≤ s'.vaddr)
         | _, _ => true)

/-- Forward bridge: the runtime check decides the proof-level invariant. -/
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
-- Layout-stage entry point.
-- ============================================================================

/-- Assign an mmap base to each object in BFS order. `ET_EXEC`
    objects keep `0`; `ET_DYN` objects start at `dynAnchor` and
    stack by `alignUp objectSpan 0x1000`. -/
def assignBases (g : ObjectList) : Array UInt64 := Id.run do
  let mut bases : Array UInt64 := Array.mkEmpty g.val.size
  let mut cursor : UInt64 := dynAnchor
  for h : i in [:g.val.size] do
    let obj := g.val[i]
    let isExec := obj.elf.header.e_type = Elaborate.ET_EXEC
    let base := if isExec then 0 else cursor
    bases := bases.push base
    if !isExec then
      cursor := cursor + alignUp (objectSpan obj.elf.loadablePhdrs) 0x1000
  return bases

section Example
open LeanLoad.Elaborate (ET_EXEC ET_DYN)

private def synthEt (name : String) (etype : UInt16) : Discover.LoadedObject :=
  let hdr : Parse.RawEhdr :=
    { (default : Parse.RawEhdr) with e_type := etype }
  let elf : Elaborate.Elf := { (default : Elaborate.Elf) with header := hdr }
  { name, path := s!"<synth:{name}>", handle := none, elf }

private def synthList (objs : Array Discover.LoadedObject) (h : 0 < objs.size) :
    Discover.ObjectList := ⟨objs, h⟩

#guard assignBases (synthList #[synthEt "main" ET_EXEC] (by simp)) = #[0]
#guard assignBases (synthList #[synthEt "lib" ET_DYN] (by simp)) = #[dynAnchor]
#guard assignBases (synthList #[synthEt "main" ET_EXEC,
                                 synthEt "libfoo" ET_DYN,
                                 synthEt "libbar" ET_DYN] (by simp))
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

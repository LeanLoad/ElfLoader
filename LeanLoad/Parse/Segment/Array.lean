/-
Checked PT_LOAD segment arrays.

`Segment.Checked` owns one segment's byte fields and per-segment invariants.
This file owns the checked array wrapper plus predicates whose subject is the
whole PT_LOAD array.

Spec: gabi 07 (`third_party/gabi/docsrc/elf/07-pheader.rst`) § Program Loading.
-/

import LeanLoad.Parse.Segment.Checked

namespace LeanLoad.Parse

-- ============================================================================
-- PT_LOAD-array well-formedness — the per-pair gabi-07 invariants on
-- `Array Segment`. Per-segment invariants are validated by `Segment.ofPhdr`.
--
-- Spec: gabi 07 § Program Loading. These are *spec-level* (gabi vaddr/memsz
-- ordering); page-aligned non-overlap is a separate runtime check via
-- `Plan.SegmentLayout` over `SegmentLayout`s.
-- ============================================================================

namespace Segments

/-- gabi 07 § Program Loading: PT_LOAD entries appear in `p_vaddr` order. -/
def Sorted (segs : Array Segment) : Prop :=
  ∀ i, ∀ _ : i < segs.size, ∀ j, ∀ _ : j < segs.size,
    i < j → segs[i].vaddr.toNat ≤ segs[j].vaddr.toNat

/-- *De facto*, not gabi-mandated: PT_LOAD `[p_vaddr, p_vaddr + p_memsz)`
    ranges are pairwise disjoint. -/
def NonOverlap (segs : Array Segment) : Prop :=
  ∀ i, ∀ _ : i < segs.size, ∀ j, ∀ _ : j < segs.size,
    i < j → segs[i].vaddr.toNat + segs[i].memsz.toNat ≤ segs[j].vaddr.toNat

end Segments

/-- Checked PT_LOAD segment array. `items` keeps the phdr order, while `sorted`
    / `nonOverlap` are the array-level facts established at checked-parse time. -/
structure Segments where
  items      : Array Segment
  sorted     : Segments.Sorted items
  nonOverlap : Segments.NonOverlap items
  deriving Repr

namespace Segments

/-- A virtual-address range contained in one checked segment satisfying `need`
    (for example, executable or readable). -/
structure VaddrRangeIn (segments : Segments) (need : Segment → Prop)
    (addr : Vaddr) (len : ByteSize) where
  index    : Fin segments.items.size
  contains : Segment.ContainsVaddrRange segments.items[index] addr len
  permits  : need segments.items[index]
  deriving Repr

/-- A file-offset range contained in one checked segment satisfying `need`. -/
structure FileRangeIn (segments : Segments) (need : Segment → Prop)
    (off : FileOff) (len : ByteSize) where
  index    : Fin segments.items.size
  contains : Segment.ContainsFileRange segments.items[index] off len
  permits  : need segments.items[index]
  deriving Repr

/-- A virtual-address range that is backed by file bytes in one checked segment
    satisfying `need`. Dynamic-table pointers use this rather than plain memory
    containment so they cannot point into BSS. -/
structure FileBackedVaddrRangeIn (segments : Segments) (need : Segment → Prop)
    (addr : Vaddr) (len : ByteSize) where
  index    : Fin segments.items.size
  contains : Segment.ContainsFileBackedVaddrRange segments.items[index] addr len
  permits  : need segments.items[index]
  deriving Repr

/-- Point membership in one checked segment satisfying `need`. Kept as an
    `abbrev` so legacy existential proofs can still destruct it directly. -/
abbrev ContainsVaddr (segments : Segments) (need : Segment → Prop) (addr : Vaddr) : Prop :=
  ∃ i, ∃ h : i < segments.items.size,
    need (segments.items[i]'h) ∧ Segment.ContainsVaddr (segments.items[i]'h) addr

abbrev ExecAddr (segments : Segments) (addr : Vaddr) : Prop :=
  ContainsVaddr segments (fun s => s.perm.exec) addr

abbrev ReadVaddrRange (segments : Segments) (addr : Vaddr) (len : ByteSize) :=
  VaddrRangeIn segments (fun s => s.perm.read) addr len

abbrev ExecVaddrRange (segments : Segments) (addr : Vaddr) (len : ByteSize) :=
  VaddrRangeIn segments (fun s => s.perm.exec) addr len

abbrev ReadFileRange (segments : Segments) (off : FileOff) (len : ByteSize) :=
  FileRangeIn segments (fun s => s.perm.read) off len

abbrev AnyFileBackedVaddrRange (segments : Segments) (addr : Vaddr) (len : ByteSize) :=
  FileBackedVaddrRangeIn segments (fun _ => True) addr len

abbrev ReadFileBackedVaddrRange (segments : Segments) (addr : Vaddr) (len : ByteSize) :=
  FileBackedVaddrRangeIn segments (fun s => s.perm.read) addr len

/-- Empty checked segment array. Useful for tests and synthetic Elfs. -/
def empty : Segments :=
  { items := #[],
    sorted := by
      intro i h_i
      simp at h_i
    nonOverlap := by
      intro i h_i
      simp at h_i }

/-- Check an array of PT_LOAD segments into the witnessed `Segments` type. -/
def ofArray (items : Array Segment) : Except String Segments :=
  letI : Decidable (Sorted items) := by
    unfold Sorted
    infer_instance
  letI : Decidable (NonOverlap items) := by
    unfold NonOverlap
    infer_instance
  if h_sorted : Sorted items then
    if h_nonOverlap : NonOverlap items then
      .ok { items, sorted := h_sorted, nonOverlap := h_nonOverlap }
    else
      .error "parse: PT_LOAD segments overlap \
        (non-overlap is de facto from linker)"
  else
    .error "parse: PT_LOAD segments not sorted \
      (gabi-07 § Program Loading: sort by p_vaddr)"

end Segments

end LeanLoad.Parse

/-
Checked PT_LOAD segment arrays.

`Segment.Basic` owns one segment's byte fields and per-segment invariants.
This file owns the checked array wrapper plus predicates whose subject is the
whole PT_LOAD array.

Spec: gabi 07 (`third_party/gabi/docsrc/elf/07-pheader.rst`) § Program Loading.
-/

import LeanLoad.Parse.LoadMap.Segment.Basic

namespace LeanLoad.Parse

-- ============================================================================
-- PT_LOAD-array well-formedness — the per-pair gabi-07 invariants on
-- `Array (Segment fileSize)`. Per-segment invariants are validated by
-- `Segment.ofPhdr`.
--
-- Spec: gabi 07 § Program Loading. These are *spec-level* (gabi eaddr/memsz
-- ordering); page-aligned non-overlap is a separate runtime check via
-- `Layout.SegmentLayout` over `SegmentLayout`s.
-- ============================================================================

namespace SegmentTable

/-- gabi 07 § Program Loading: PT_LOAD entries appear in `p_vaddr` order. -/
def Sorted {fileSize : ByteSize} (segs : Array (Segment fileSize)) : Prop :=
  ∀ i, ∀ _ : i < segs.size, ∀ j, ∀ _ : j < segs.size,
    i < j → segs[i].eaddr.toNat ≤ segs[j].eaddr.toNat

/-- *De facto*, not gabi-mandated: PT_LOAD `[p_vaddr, p_vaddr + p_memsz)`
    ranges are pairwise disjoint. -/
def NonOverlap {fileSize : ByteSize} (segs : Array (Segment fileSize)) : Prop :=
  ∀ i, ∀ _ : i < segs.size, ∀ j, ∀ _ : j < segs.size,
    i < j → segs[i].eaddr.toNat + segs[i].memsz.toNat ≤ segs[j].eaddr.toNat

end SegmentTable

/-- Checked PT_LOAD segment array. `items` keeps the phdr order, while `sorted`
    / `nonOverlap` are the array-level facts established at checked-parse time. -/
structure SegmentTable (fileSize : ByteSize) where
  private mk ::
  items      : Array (Segment fileSize)
  sorted     : SegmentTable.Sorted items
  nonOverlap : SegmentTable.NonOverlap items
  deriving Repr

namespace SegmentTable

/-- Empty checked segment array. Useful for tests and synthetic Elfs. -/
def empty {fileSize : ByteSize} : SegmentTable fileSize :=
  { items := #[],
    sorted := by
      intro i h_i
      simp at h_i
    nonOverlap := by
      intro i h_i
      simp at h_i }

/-- Check an array of PT_LOAD segments into the witnessed `SegmentTable` type. -/
def ofArray {fileSize : ByteSize} (items : Array (Segment fileSize)) :
    Except String (SegmentTable fileSize) :=
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

end SegmentTable

end LeanLoad.Parse

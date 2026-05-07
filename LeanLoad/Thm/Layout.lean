/-
Layout-stage theorems.

- `g.layouts` produces one layout per object on the success branch
  (the size invariant is in its return subtype) and additionally
  packages a per-layout `segmentsSorted` proof — see `Layout.lean`.
- `objectSpan` upper-bounds every segment (containment); sorted
  segments ⇒ pairwise disjoint.
- `segmentsSortedB ↔ segmentsSorted` (decidable Bool ⇔ Prop) is the
  audited bridge from the runtime check `g.layouts` runs to the
  proof-level invariant downstream code consumes.

The trust seam is now structural: there's no axiomatic `WellFormedElf`
side-condition. `g.layouts` either rejects an ELF whose page-aligned
`PT_LOAD` ranges are not sorted/non-overlapping, or returns a witness
that they are. gabi 07 mandates the sort; non-overlap is de facto
(every linker produces it; `Map.lean`'s `MAP_FIXED` mmap requires it
for correctness). The runtime check enforces both.
-/

import LeanLoad.Plan.Layout

namespace LeanLoad.Thm

open LeanLoad.Layout
open LeanLoad.Discover
open LeanLoad.Parse.Segment

/-- Each segment's `endAddr` is bounded by its object's `objectSpan`.
    The `foldl max 0` upper-bound, lifted to every input element. -/
theorem segment_endAddr_le_objectSpan
    (lyt : ObjectLayout) (i : Nat) (h : i < lyt.segments.size) :
    lyt.segments[i].endAddr ≤ objectSpan lyt.segments := by
  let motive : Nat → UInt64 → Prop := fun n acc =>
    ∀ k (_ : k < n) (_ : k < lyt.segments.size),
      lyt.segments[k].endAddr ≤ acc
  suffices motive lyt.segments.size (objectSpan lyt.segments) from this i h h
  unfold objectSpan
  refine Array.foldl_induction motive ?_ ?_
  · intros _ hk _; omega
  · intro idx b ih k hk hk'
    by_cases hkj : k = idx.val
    · have hindex : lyt.segments[k] = lyt.segments[idx] := by congr 1
      rw [hindex]
      show _ ≤ ite _ _ _
      split
      · exact UInt64.le_refl _
      · rename_i hnle; exact (UInt64.le_total b _).resolve_left hnle
    · have hk_lt : k < idx.val :=
        Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk) hkj
      have prev_le : lyt.segments[k].endAddr ≤ b := ih k hk_lt hk'
      show _ ≤ ite _ _ _
      split
      · rename_i hb_le; exact UInt64.le_trans prev_le hb_le
      · exact prev_le

/-- Sorted segments ⇒ pairwise disjoint. With `endAddr[i] ≤ vaddr[j]`
    for `i < j`, every distinct pair satisfies `Segment.disjoint`. -/
theorem segmentsPairwiseDisjoint_of_segmentsSorted
    (lyt : ObjectLayout) (h : lyt.segmentsSorted) :
    lyt.segmentsPairwiseDisjoint := by
  intro i j hi hj hne
  rcases Nat.lt_or_ge i j with hlt | hge
  · exact Or.inl (h i j hi hj hlt)
  · have hgt : j < i := Nat.lt_of_le_of_ne hge (Ne.symm hne)
    exact Or.inr (h j i hj hi hgt)

-- ============================================================================
-- Bool ↔ Prop bridge for the runtime well-formedness check.
-- ============================================================================

/-- The runtime check is sound: `segmentsSortedB` rejects every layout
    whose page-aligned segments are not sorted with non-overlapping
    `[vaddr, endAddr)` ranges.

    This is the converse of `segmentsSorted_of_segmentsSortedB`
    (defined in `Layout.lean` so `g.layouts` can use it inline). -/
theorem ObjectLayout.segmentsSortedB_of_segmentsSorted
    (lyt : ObjectLayout) (h : lyt.segmentsSorted) :
    lyt.segmentsSortedB = true := by
  unfold ObjectLayout.segmentsSortedB
  rw [List.all_eq_true]
  intro i hi
  rw [List.all_eq_true]
  intro j hj
  rw [List.mem_range] at hi hj
  by_cases hlt : i < j
  · have hle := h i j hi hj hlt
    rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hj]
    simp [hle]
  · simp [hlt]

/-- Full equivalence: the decidable Bool check decides the proof-level
    invariant. `g.layouts` can therefore use `segmentsSortedB` at
    runtime and pack a `segmentsSorted` witness into its return type
    without any unproved bridge. -/
theorem ObjectLayout.segmentsSortedB_iff_segmentsSorted (lyt : ObjectLayout) :
    lyt.segmentsSortedB = true ↔ lyt.segmentsSorted :=
  ⟨ObjectLayout.segmentsSorted_of_segmentsSortedB lyt,
   ObjectLayout.segmentsSortedB_of_segmentsSorted lyt⟩

-- ============================================================================
-- Disjointness for free from the witness `g.layouts` produces.
-- ============================================================================

/-- Every layout in `g.layouts`' success array has pairwise disjoint
    segments. Combines the per-layout `segmentsSorted` witness packed
    into the return subtype with `segmentsPairwiseDisjoint_of_segmentsSorted`.
    No `WellFormedElf` hypothesis required — the runtime check at
    `g.layouts` is the structural witness. -/
theorem ObjectList.layouts_segmentsPairwiseDisjoint
    (g : ObjectList)
    {a : Array ObjectLayout}
    (h : a.size = g.val.size ∧ ∀ (i : Nat) (hi : i < a.size), a[i].segmentsSorted)
    (i : Nat) (hi : i < a.size) :
    a[i].segmentsPairwiseDisjoint :=
  segmentsPairwiseDisjoint_of_segmentsSorted _ (h.right i hi)

end LeanLoad.Thm

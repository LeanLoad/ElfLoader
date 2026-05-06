/-
Layout-stage theorems.

- `g.layouts` produces one layout per object (refinement-seam shape).
- `objectSpan` upper-bounds every segment (containment); sorted
  segments ⇒ pairwise disjoint.

The "sorted from PT_LOAD invariant" half — the discharge that lets
`segmentsPairwiseDisjoint_of_segmentsSorted` apply to a real ELF —
is future work; gabi 07 implies but doesn't formally state PT_LOAD
non-overlap.
-/

import LeanLoad.Layout

namespace LeanLoad.Thm

open LeanLoad.Layout
open LeanLoad.Discover

/-- `g.layouts` produces one layout per discovered object — no
    drops, no duplicates. -/
theorem layouts_size (g : DepGraph) : g.layouts.size = g.objects.size := by
  simp [DepGraph.layouts]

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

end LeanLoad.Thm

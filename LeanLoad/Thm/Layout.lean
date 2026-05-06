/-
Layout-stage theorems.

- `g.layouts` produces one layout per object on the success branch.
- `objectSpan` upper-bounds every segment (containment); sorted
  segments ⇒ pairwise disjoint.

`WellFormedElf` is the trust seam between the parsed ELF and the
disjointness theorem. It bundles one assumption — PT_LOAD entries
sorted by `p_vaddr` with non-overlapping ranges. gabi 07 § Program
Loading mandates the sort; non-overlap is a de facto convention
(every linker produces it; the loader's `Map.lean` relies on it for
`MAP_FIXED` mmap correctness) but isn't formally stated by gabi.
We take it as an axiomatic well-formedness assumption. The runtime
check `Parse.Segment.wellFormed` decides it; if every object
satisfies it, `g.layouts` returns `.ok` and the disjointness
theorems apply.
-/

import LeanLoad.Layout

namespace LeanLoad.Thm

open LeanLoad.Layout
open LeanLoad.Discover
open LeanLoad.Parse.Segment

-- The "one layout per object" property is now in the *return type* of
-- `g.layouts`: it returns `Except String { a : Array ObjectLayout //
-- a.size = g.objects.size }`. The size proof is the second component
-- of the subtype — no separate theorem needed.

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
-- WellFormedElf: trust seam for segment disjointness.
-- ============================================================================

/-- Well-formedness predicate on a parsed ELF. Bundles the PT_LOAD
    invariant that the loader relies on:

    - **Sorted (gabi 07 mandated)**: PT_LOAD entries appear in
      ascending order of `p_vaddr`.
    - **Non-overlapping (de facto, not gabi-mandated)**: their
      `[vaddr, endAddr)` ranges are pairwise disjoint. Every linker
      produces this; `Map.lean`'s `MAP_FIXED` mmap requires it for
      correctness; gabi 07 doesn't formally state it. We treat it as
      a trust assumption — `WellFormedElf elf` is the witness that a
      caller can supply.

    Combined into one condition (`endAddr[i] ≤ vaddr[j]` for `i < j`),
    matching `ObjectLayout.segmentsSorted`. -/
structure WellFormedElf (elf : Parse.File.ParsedElf) : Prop where
  segmentsSorted :
    ∀ i j (_ : i < (segmentsOf elf).size) (_ : j < (segmentsOf elf).size),
      i < j → (segmentsOf elf)[i].endAddr ≤ (segmentsOf elf)[j].vaddr

/-- Discharge `ObjectLayout.segmentsSorted` from `WellFormedElf` for
    any layout produced via `objectLayout` from the same ELF. -/
theorem ObjectLayout.segmentsSorted_of_wellFormed
    (isMain : Bool) (base : UInt64)
    (elf : Parse.File.ParsedElf) (h : WellFormedElf elf) :
    (objectLayout isMain base elf).segmentsSorted := by
  intro i j hi hj hlt
  exact h.segmentsSorted i j hi hj hlt

/-- End-to-end: a `WellFormedElf` discharges segment pairwise
    disjointness on any layout built from it. -/
theorem ObjectLayout.segmentsPairwiseDisjoint_of_wellFormed
    (isMain : Bool) (base : UInt64)
    (elf : Parse.File.ParsedElf) (h : WellFormedElf elf) :
    (objectLayout isMain base elf).segmentsPairwiseDisjoint :=
  segmentsPairwiseDisjoint_of_segmentsSorted _
    (segmentsSorted_of_wellFormed isMain base elf h)

end LeanLoad.Thm

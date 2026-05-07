/-
PT_LOAD-array well-formedness — the *per-pair* gabi-07 invariants
(`Sorted` + de-facto `NonOverlap`) on the spec-level `RawSegment`
view. Per-segment invariants (`fileszLeMemsz`, `alignPow2`,
`alignCong`, address bound) live as fields on `RawSegment` itself.

Spec: gabi 07 (`third_party/gabi/docsrc/elf/07-pheader.rst`) § Program
Loading.

WellFormed is a *spec-level* property: it's about gabi vaddr/memsz
ordering, not the loader's page-aligned ranges. (Page-aligned
non-overlap is a separate runtime check on `ObjectLayout` —
`segmentsSortedB`.) Building it on `Array RawSegment` makes that
layering explicit; the loader-stage `Segment` extends `RawSegment`,
so `WellFormed (segments.map (·.toRawSegment))` lifts naturally.
-/

import LeanLoad.Elaborate.RawSegment

namespace LeanLoad.Elaborate

-- ============================================================================
-- Per-pair invariants. Bound the index in front of the quantifier so
-- each Prop is decidable via `Nat.decidableBAllLT`.
-- ============================================================================

/-- gabi 07 § Program Loading: PT_LOAD entries appear in `p_vaddr` order. -/
def Sorted (segs : Array RawSegment) : Prop :=
  ∀ i, ∀ _ : i < segs.size, ∀ j, ∀ _ : j < segs.size,
    i < j → segs[i].vaddr ≤ segs[j].vaddr

/-- *De facto*, not gabi-mandated: PT_LOAD `[p_vaddr, p_vaddr +
    p_memsz)` ranges are pairwise disjoint. -/
def NonOverlap (segs : Array RawSegment) : Prop :=
  ∀ i, ∀ _ : i < segs.size, ∀ j, ∀ _ : j < segs.size,
    i < j → segs[i].vaddr + segs[i].memsz ≤ segs[j].vaddr

instance (segs : Array RawSegment) : Decidable (Sorted segs) := by
  unfold Sorted; infer_instance
instance (segs : Array RawSegment) : Decidable (NonOverlap segs) := by
  unfold NonOverlap; infer_instance

-- ============================================================================
-- The bundle.
-- ============================================================================

/-- The PT_LOAD segments satisfy the per-pair gabi-07 mandates plus
    the de-facto non-overlap convention. Per-segment mandates live
    on `RawSegment` itself. Built by `elaborate` against the gabi
    spec view and carried on `Elf.segmentsWf` so downstream consumers
    don't re-check. -/
structure WellFormed (segs : Array RawSegment) : Prop where
  sorted     : Sorted segs
  nonOverlap : NonOverlap segs

instance (segs : Array RawSegment) : Decidable (WellFormed segs) :=
  decidable_of_iff (Sorted segs ∧ NonOverlap segs)
    ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩

theorem WellFormed_nil : WellFormed (#[] : Array RawSegment) := by decide

end LeanLoad.Elaborate

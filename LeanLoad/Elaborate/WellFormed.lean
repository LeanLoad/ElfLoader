/-
PT_LOAD-array well-formedness — the *per-pair* gabi-07 invariants
(`Sorted` + de-facto `NonOverlap`). Per-segment invariants
(`fileszLeMemsz`, `alignPow2`, `alignCong`, address bound) live as
fields on `Elaborate.Segment` itself, so they flow through the
pipeline without re-checking.

Spec: gabi 07 (`third_party/gabi/docsrc/elf/07-pheader.rst`) § Program
Loading.

`WellFormed` is a Prop-valued structure; field projections give
per-pair access without auxiliary theorems. A `Decidable` instance
lets `elaborate` check the bundle at runtime and carry the witness
into `Elf.segmentsWf`.
-/

import LeanLoad.Elaborate.Segment

namespace LeanLoad.Elaborate

-- ============================================================================
-- Per-pair invariants. Bound the index in front of the quantifier so
-- each Prop is decidable via `Nat.decidableBAllLT`.
-- ============================================================================

/-- gabi 07 § Program Loading: PT_LOAD entries appear in `p_vaddr` order. -/
def Sorted (segs : Array Segment) : Prop :=
  ∀ i, ∀ _ : i < segs.size, ∀ j, ∀ _ : j < segs.size,
    i < j → segs[i].vaddr ≤ segs[j].vaddr

/-- *De facto*, not gabi-mandated: PT_LOAD `[p_vaddr, p_vaddr +
    p_memsz)` ranges are pairwise disjoint. -/
def NonOverlap (segs : Array Segment) : Prop :=
  ∀ i, ∀ _ : i < segs.size, ∀ j, ∀ _ : j < segs.size,
    i < j → segs[i].vaddr + segs[i].memsz ≤ segs[j].vaddr

instance (segs : Array Segment) : Decidable (Sorted segs) := by
  unfold Sorted; infer_instance
instance (segs : Array Segment) : Decidable (NonOverlap segs) := by
  unfold NonOverlap; infer_instance

-- ============================================================================
-- The bundle.
-- ============================================================================

/-- The PT_LOAD segments satisfy the per-pair gabi-07 mandates plus
    the de-facto non-overlap convention. Per-segment mandates live
    on `Segment` itself. Built by `elaborate` and carried on
    `Elf.segmentsWf` so downstream consumers don't re-check. -/
structure WellFormed (segs : Array Segment) : Prop where
  sorted     : Sorted segs
  nonOverlap : NonOverlap segs

instance (segs : Array Segment) : Decidable (WellFormed segs) :=
  decidable_of_iff (Sorted segs ∧ NonOverlap segs)
    ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩

theorem WellFormed_nil : WellFormed (#[] : Array Segment) := by decide

end LeanLoad.Elaborate

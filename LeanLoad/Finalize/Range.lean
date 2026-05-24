/-
Pure address-range predicates.

These predicates describe half-open UInt64 address intervals after lifting
endpoints to `Nat`, so containment/disjointness proofs do not depend on
UInt64 wraparound semantics. They are used by the finalize-stage safety witness;
the Runtime stage only consumes already-witnessed load ops.
-/

namespace LeanLoad.Finalize.Range

/-- Two address ranges do not overlap. -/
def Disjoint (a₁ l₁ a₂ l₂ : UInt64) : Prop :=
  a₁.toNat + l₁.toNat ≤ a₂.toNat ∨ a₂.toNat + l₂.toNat ≤ a₁.toNat

/-- An address range `[innerA, innerA+innerL)` is fully contained in
    `[outerA, outerA+outerL)`. -/
def InRange (innerA innerL outerA outerL : UInt64) : Prop :=
  outerA.toNat ≤ innerA.toNat ∧
  innerA.toNat + innerL.toNat ≤ outerA.toNat + outerL.toNat

instance (a₁ l₁ a₂ l₂ : UInt64) : Decidable (Disjoint a₁ l₁ a₂ l₂) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance (innerA innerL outerA outerL : UInt64) :
    Decidable (InRange innerA innerL outerA outerL) :=
  inferInstanceAs (Decidable (_ ∧ _))

end LeanLoad.Finalize.Range

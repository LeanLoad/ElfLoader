/-
Relocation theorems.

`formula_size_valid` proves that the per-arch formula dispatcher
(`Spec.Reloc.formulaFor`) only emits writes of size 4 or 8. Per-arch
unfoldings happen inline as branches of one proof.

Lifting this to a planner-level statement (every write from
`Reloc.plan` has size ∈ {4, 8}) requires for-loop / `Except`-monad
reasoning we haven't built up yet — the new `plan` is `Except String
(Array Patch)` to support per-stage OOB rejection. Future work.

Per-type sample outputs are checked at elaboration via `#guard`s
next to each `formula` def.
-/

import LeanLoad.Spec.Reloc.Formula
import LeanLoad.Reloc

namespace LeanLoad.Thm

open LeanLoad.Reloc

/-- Every write produced by the per-arch dispatcher has width 4 or 8.
    Covers AArch64 and x86-64 in one theorem; per-arch unfoldings are
    inline branches of the proof. -/
theorem formula_size_valid {em : UInt16} {f : Formula}
    (hf : Spec.Reloc.formulaFor em = some f)
    (ty : UInt32) (inp : FormulaInputs) (r : FormulaResult) :
    f ty inp = some r → r.size = 4 ∨ r.size = 8 := by
  intro h
  unfold Spec.Reloc.formulaFor at hf
  split at hf
  · -- AArch64 branch
    injection hf with hf; subst hf
    unfold Spec.Reloc.Aarch64.formula at h
    repeat' split at h
    all_goals first
      | contradiction
      | (injection h with hr; subst hr; first | (right; rfl) | (left; rfl))
  · split at hf
    · -- x86-64 branch
      injection hf with hf; subst hf
      unfold Spec.Reloc.X86_64.formula at h
      repeat' split at h
      all_goals first
        | contradiction
        | (injection h with hr; subst hr; first | (right; rfl) | (left; rfl))
    · contradiction

end LeanLoad.Thm

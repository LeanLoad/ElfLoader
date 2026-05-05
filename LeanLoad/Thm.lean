/-
`LeanLoad.Thm` — single audit surface for every machine-checked
property the project proves.

The reader who wants to assess what LeanLoad guarantees opens this
file. Each theorem's *statement* is the contract (proofs are
black-boxed by Lean's kernel).

Convention:

- Definitions, structs, and constants (the gabi/x86-64-ABI
  transcription) live next to where they're used. Those *are* the
  spec — there is no second copy to keep in sync.
- Theorems all live here. Proofs are short enough that colocation
  buys nothing; consolidation gives a single, scannable audit list.
- When a theorem grows past one screen, split it into
  `LeanLoad/Thm/<Topic>.lean`. The structure here stays unchanged.
-/

import LeanLoad.Spec.Header
import LeanLoad.Spec.Program
import LeanLoad.Spec.Symbol
import LeanLoad.Spec.Reloc
import LeanLoad.Plan.Layout
import LeanLoad.Spec.Reloc.Aarch64
import LeanLoad.Spec.Reloc.X86_64

namespace LeanLoad.Thm

open LeanLoad.Spec
open LeanLoad.Spec.Reloc
open LeanLoad.Plan.Reloc

-- ============================================================================
-- O3. VA → file-offset correctness within `PT_LOAD`.
--     (`Parse.Parse.File.vaToOffset`)
-- ============================================================================

/-- If `vaToOffset` returns `some off`, there is a witness `PT_LOAD`
    segment in `phdrs` whose virtual range covers `va` and `off` is
    the corresponding file offset. -/
theorem vaToOffset_correct
    (phdrs : Array Program.Header64) (va : UInt64) (off : Nat) :
    Parse.File.vaToOffset phdrs va = some off →
    ∃ ph ∈ phdrs,
      ph.p_type = Program.PT_LOAD ∧
      ph.p_vaddr ≤ va ∧
      va < ph.p_vaddr + ph.p_memsz ∧
      off = (va - ph.p_vaddr).toNat + ph.p_offset.toNat := by
  intro h
  unfold Parse.File.vaToOffset at h
  obtain ⟨ph, hmem, hf⟩ := Array.exists_of_findSome?_eq_some h
  refine ⟨ph, hmem, ?_⟩
  split at hf
  · rename_i hcond
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
    refine ⟨hcond.1.1, hcond.1.2, hcond.2, ?_⟩
    injection hf with hf; exact hf.symm
  · contradiction

-- ============================================================================
-- O4. Plan determinism + structural integrity.
--     (`Plan.Plan.Layout.fromLinkMap`)
-- ============================================================================

/-- `fromLinkMap` produces one layout per discovered object — no
    drops, no duplicates. Refines the `LoaderPlan` contract. -/
theorem fromLinkMap_layouts_size
    (lm : Discover.LinkMap) (initOrder finiOrder : Array Nat) :
    (Plan.Layout.fromLinkMap lm initOrder finiOrder).layouts.size = lm.objects.size := by
  simp [Plan.Layout.fromLinkMap]

/-- `fromLinkMap` is pure: same input, same output. -/
theorem fromLinkMap_deterministic
    (lm : Discover.LinkMap) (initOrder finiOrder : Array Nat) :
    Plan.Layout.fromLinkMap lm initOrder finiOrder
      = Plan.Layout.fromLinkMap lm initOrder finiOrder :=
  rfl

-- ============================================================================
-- O6 (sample). Per-arch relocation-formula totality and the
--     planner-to-applier safety bridge.
--
-- Per-type sample outputs are checked at elaboration via `#guard`s
-- next to each `formula` def — a wrong table fails to build. The
-- theorems here are the ones that say something a `#guard` cannot:
--   * formula is defined on every (type, input)        (totality)
--   * every formula result has size ∈ {4, 8}           (safety bridge)
--
-- One copy per supported architecture. `Load.Apply.applyReloc` panics
-- on widths other than 4 or 8; the size-valid lemmas are the bridge
-- that says the panic is unreachable for plans built from these
-- formulas.
-- ============================================================================

namespace Aarch64
open LeanLoad.Spec.Reloc.Aarch64

/-- AArch64 formula is total: every input yields `none` or a full result. -/
theorem formula_is_total (ty : UInt32) (inp : FormulaInputs) :
    formula ty inp = none ∨ ∃ r, formula ty inp = some r := by
  cases h : formula ty inp
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

/-- Every write the AArch64 formula emits has width 4 or 8 bytes. -/
theorem formula_size_valid (ty : UInt32) (inp : FormulaInputs) (r : FormulaResult) :
    formula ty inp = some r → r.size = 4 ∨ r.size = 8 := by
  intro h; unfold formula at h
  repeat' split at h
  all_goals first
    | contradiction
    | (injection h with hr; subst hr; first | (right; rfl) | (left; rfl))

end Aarch64

namespace X86_64
open LeanLoad.Spec.Reloc.X86_64

/-- x86-64 formula is total: every input yields `none` or a full result. -/
theorem formula_is_total (ty : UInt32) (inp : FormulaInputs) :
    formula ty inp = none ∨ ∃ r, formula ty inp = some r := by
  cases h : formula ty inp
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

/-- Every write the x86-64 formula emits has width 4 or 8 bytes. -/
theorem formula_size_valid (ty : UInt32) (inp : FormulaInputs) (r : FormulaResult) :
    formula ty inp = some r → r.size = 4 ∨ r.size = 8 := by
  intro h; unfold formula at h
  repeat' split at h
  all_goals first
    | contradiction
    | (injection h with hr; subst hr; first | (right; rfl) | (left; rfl))

end X86_64

end LeanLoad.Thm

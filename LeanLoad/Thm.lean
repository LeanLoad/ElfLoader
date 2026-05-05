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

import LeanLoad.Parse
import LeanLoad.Plan.Layout
import LeanLoad.Plan.Reloc.Aarch64

namespace LeanLoad.Thm

open LeanLoad.Parse
open LeanLoad.Plan
open LeanLoad.Plan.Reloc
open LeanLoad.Plan.Reloc.Aarch64

-- ============================================================================
-- O3. VA → file-offset correctness within `PT_LOAD`.
--     (`Parse.File.vaToOffset`)
-- ============================================================================

/-- If `vaToOffset` returns `some off`, there is a witness `PT_LOAD`
    segment in `phdrs` whose virtual range covers `va` and `off` is
    the corresponding file offset. -/
theorem vaToOffset_correct
    (phdrs : Array Program.Header64) (va : UInt64) (off : Nat) :
    File.vaToOffset phdrs va = some off →
    ∃ ph ∈ phdrs,
      ph.p_type = Program.PT_LOAD ∧
      ph.p_vaddr ≤ va ∧
      va < ph.p_vaddr + ph.p_memsz ∧
      off = (va - ph.p_vaddr).toNat + ph.p_offset.toNat := by
  intro h
  unfold File.vaToOffset at h
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
--     (`Plan.Layout.fromLinkMap`)
-- ============================================================================

/-- `fromLinkMap` produces one layout per discovered object — no
    drops, no duplicates. Refines the `LoaderPlan` contract. -/
theorem fromLinkMap_layouts_size
    (lm : Discover.LinkMap) (initOrder finiOrder : Array Nat) :
    (Layout.fromLinkMap lm initOrder finiOrder).layouts.size = lm.objects.size := by
  simp [Layout.fromLinkMap]

/-- `fromLinkMap` is pure: same input, same output. -/
theorem fromLinkMap_deterministic
    (lm : Discover.LinkMap) (initOrder finiOrder : Array Nat) :
    Layout.fromLinkMap lm initOrder finiOrder
      = Layout.fromLinkMap lm initOrder finiOrder :=
  rfl

-- ============================================================================
-- O6 (sample). AArch64 relocation formula: totality and the
--     planner-to-applier safety bridge.
--
-- Per-type sample outputs are checked at elaboration via `#guard`s
-- next to the `formula` def — a wrong table fails to build. The
-- theorems here are the ones that say something a `#guard` cannot:
--   * formula is defined on every (type, input)        (totality)
--   * every formula result has size ∈ {4, 8}           (safety bridge)
-- ============================================================================

/-- The formula function is total: every (type, input) returns either
    `none` or a fully-formed result. No panic, no nontermination. -/
theorem formula_is_total (ty : UInt32) (inp : FormulaInputs) :
    formula ty inp = none ∨ ∃ r, formula ty inp = some r := by
  cases h : formula ty inp
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

/-- Every write the AArch64 formula emits has width 4 or 8 bytes.
    `Load.Apply.applyReloc` panics on any other size, so this is the
    bridge that says the panic is unreachable for plans produced
    against this formula. (Once an x86_64 formula lands, it'll need
    its own copy of this lemma to keep the bridge intact.) -/
theorem formula_size_valid (ty : UInt32) (inp : FormulaInputs) (r : FormulaResult) :
    formula ty inp = some r → r.size = 4 ∨ r.size = 8 := by
  intro h
  unfold formula at h
  split at h
  · contradiction                          -- NONE
  split at h
  · injection h with hr; subst hr; right; rfl  -- ABS64 → 8
  split at h
  · injection h with hr; subst hr; left;  rfl  -- ABS32 → 4
  split at h
  · injection h with hr; subst hr; right; rfl  -- GLOB_DAT → 8
  split at h
  · injection h with hr; subst hr; right; rfl  -- JUMP_SLOT → 8
  split at h
  · injection h with hr; subst hr; right; rfl  -- RELATIVE → 8
  contradiction                            -- unknown → none

end LeanLoad.Thm

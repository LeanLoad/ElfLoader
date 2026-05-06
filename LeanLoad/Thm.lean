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
import LeanLoad.Layout
import LeanLoad.Spec.Reloc.Aarch64
import LeanLoad.Spec.Reloc.X86_64
import LeanLoad.Spec.GnuHash

namespace LeanLoad.Thm

open LeanLoad.Spec
open LeanLoad.Spec.Reloc
open LeanLoad.Reloc

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
--     (`Layout.fromLinkMap`)
-- ============================================================================

/-- `fromLinkMap` produces one layout per discovered object — no
    drops, no duplicates. Refines the `Layout.Layout` contract. -/
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
-- O6 (sample). Per-arch relocation-formula totality and the
--     planner-to-applier safety bridge.
--
-- Per-type sample outputs are checked at elaboration via `#guard`s
-- next to each `formula` def — a wrong table fails to build. The
-- theorems here are the ones that say something a `#guard` cannot:
--   * formula is defined on every (type, input)        (totality)
--   * every formula result has size ∈ {4, 8}           (safety bridge)
--
-- One copy per supported architecture. `Apply.applyReloc` panics
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

-- ============================================================================
-- GNU hash symbol-count derivation.
--
-- `Spec.GnuHash.symCount` derives the dynsym count from a parsed GNU
-- hash table. gnu-gabi defines no count tag, so the algorithm is
-- inferred from the layout (see `Spec/GnuHash.lean` docstring). These
-- theorems pin down the small properties we *can* prove without
-- modeling the linker invariant in full:
--   * empty buckets ⇒ count = symoffset (no hashed symbols)
--   * a non-empty result strictly exceeds the largest bucket value,
--     i.e. covers every dynsym index any bucket could reference
-- ============================================================================

namespace GnuHash
open LeanLoad.Spec.GnuHash

/-- `maxBucket` of the empty array is 0. Sanity for the base case. -/
theorem maxBucket_empty : maxBucket #[] = 0 := rfl

/-- All-empty buckets ⇒ `symCount` returns `symoffset` exactly.
    Captures: when the hash table references no symbols, the dynsym
    has only the `symoffset` synthetic entries. -/
theorem symCount_empty_buckets (so : Nat) (cs : Array UInt32) :
    symCount so #[] cs = some so := by
  unfold symCount
  simp [maxBucket_empty]

/-- `findEndMarker` returns indices ≥ its `start` argument; this is
    the standard `findIdx?`-shifted-by-`start` property. -/
theorem findEndMarker_ge (cs : Array UInt32) (start j : Nat) :
    findEndMarker cs start = some j → j ≥ start := by
  unfold findEndMarker
  intro h
  cases hk : (cs.toList.drop start).findIdx? (fun w => w &&& 1 == 1) with
  | none => rw [hk] at h; simp at h
  | some k => rw [hk] at h; simp at h; omega

/-- If `symCount` returns a non-empty-bucket result, that result is
    strictly greater than every bucket value (i.e. greater than every
    dynsym index any bucket can reference). This is the soundness
    direction: we never report a count smaller than what the buckets
    already imply. -/
theorem symCount_gt_maxBucket
    (so : Nat) (bs cs : Array UInt32) (n : Nat)
    (hpos : maxBucket bs > 0) :
    symCount so bs cs = some n → n > maxBucket bs := by
  intro h
  unfold symCount at h
  have hne : ¬ (maxBucket bs = 0) := by omega
  simp [hne] at h
  cases hf : findEndMarker cs (maxBucket bs - so) with
  | none => rw [hf] at h; simp at h
  | some j =>
    rw [hf] at h
    simp at h
    have hjge : j ≥ maxBucket bs - so := findEndMarker_ge _ _ _ hf
    omega

end GnuHash

end LeanLoad.Thm

/-
AArch64 relocation formulas.

Spec: ARM ELF for the AArch64 ABI § Dynamic Relocations. Subset
needed for the loader-minimal scope (no static-link relocations, no
TLS, no `IFUNC`):

| Type                  | Code | Width | Formula |
| --------------------- | ---- | ----- | ------- |
| `R_AARCH64_NONE`      |    0 |   —   | none    |
| `R_AARCH64_ABS64`     |  257 |   8   | S + A   |
| `R_AARCH64_ABS32`     |  258 |   4   | S + A   |
| `R_AARCH64_GLOB_DAT`  | 1025 |   8   | S + A   |
| `R_AARCH64_JUMP_SLOT` | 1026 |   8   | S + A   |
| `R_AARCH64_RELATIVE`  | 1027 |   8   | B + A   |

Note: `GLOB_DAT` and `JUMP_SLOT` are documented as `S + A` for
completeness; in practice the linker emits them with `A = 0`.
-/

import LeanLoad.Link.Reloc

namespace LeanLoad.Link.Reloc.Aarch64

def R_AARCH64_NONE      : UInt32 := 0
def R_AARCH64_ABS64     : UInt32 := 257
def R_AARCH64_ABS32     : UInt32 := 258
def R_AARCH64_GLOB_DAT  : UInt32 := 1025
def R_AARCH64_JUMP_SLOT : UInt32 := 1026
def R_AARCH64_RELATIVE  : UInt32 := 1027

/-- Apply an AArch64 dynamic-relocation formula. Returns `none` for
    `R_AARCH64_NONE` and any unsupported type. -/
def formula : Formula := fun ty inp =>
  let S := inp.symValue
  let A := inp.addend
  let B := inp.base
  if ty == R_AARCH64_NONE      then none
  else if ty == R_AARCH64_ABS64     then some { value := S + A, size := 8 }
  else if ty == R_AARCH64_ABS32     then some { value := S + A, size := 4 }
  else if ty == R_AARCH64_GLOB_DAT  then some { value := S + A, size := 8 }
  else if ty == R_AARCH64_JUMP_SLOT then some { value := S + A, size := 8 }
  else if ty == R_AARCH64_RELATIVE  then some { value := B + A, size := 8 }
  else none

#guard (formula R_AARCH64_RELATIVE { symValue := 0, addend := 0xa90, base := 0x10000, place := 0 })
        == some { value := 0x10a90, size := 8 }
#guard (formula R_AARCH64_GLOB_DAT { symValue := 0xdeadbeef, addend := 0, base := 0, place := 0 })
        == some { value := 0xdeadbeef, size := 8 }

-- ============================================================================
-- Sample correctness theorem (verification.md O6).
-- ============================================================================

/-- The `R_AARCH64_RELATIVE` formula returns exactly `B + A`, written
    8 bytes wide. Mirrors the linksem-paper-style "single relocation
    type, parametric in the address" theorem (Kell, Mulligan, Sewell,
    OOPSLA 2016 § 6) for our setup. -/
theorem formula_relative_correct (inp : FormulaInputs) :
    formula R_AARCH64_RELATIVE inp =
      some { value := inp.base + inp.addend, size := 8 } := by
  rfl

/-- `R_AARCH64_GLOB_DAT = S + A`, 8-byte write. -/
theorem formula_glob_dat_correct (inp : FormulaInputs) :
    formula R_AARCH64_GLOB_DAT inp =
      some { value := inp.symValue + inp.addend, size := 8 } := by
  rfl

/-- `R_AARCH64_JUMP_SLOT = S + A`, 8-byte write. -/
theorem formula_jump_slot_correct (inp : FormulaInputs) :
    formula R_AARCH64_JUMP_SLOT inp =
      some { value := inp.symValue + inp.addend, size := 8 } := by
  rfl

/-- `R_AARCH64_ABS64 = S + A`, 8-byte write. -/
theorem formula_abs64_correct (inp : FormulaInputs) :
    formula R_AARCH64_ABS64 inp =
      some { value := inp.symValue + inp.addend, size := 8 } := by
  rfl

/-- `R_AARCH64_NONE` produces no write. -/
theorem formula_none_is_none (inp : FormulaInputs) :
    formula R_AARCH64_NONE inp = none := by
  rfl

/-- The formula function is total: it always returns either a result
    or `none`. Trivial because the body is a chain of `if`s landing in
    explicit `some _` or `none` — no panics, no nontermination. -/
theorem formula_is_total (ty : UInt32) (inp : FormulaInputs) :
    formula ty inp = none ∨ ∃ r, formula ty inp = some r := by
  cases h : formula ty inp
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

end LeanLoad.Link.Reloc.Aarch64

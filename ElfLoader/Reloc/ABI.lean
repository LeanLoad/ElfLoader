/-
ABI relocation formulas — gabi-06 abstract `(S, A, B, P)` inputs, the
per-arch tables, and the per-`e_machine` dispatcher.

Three sections, layered:

1. **Abstract types** — `PatchSize`, `FormulaInputs`, `FormulaResult`,
   `Formula`. The shape every per-arch table conforms to.

2. **Per-arch tables** — `Aarch64.formula` (ARM ELF for AArch64 ABI §
   Dynamic Relocations) and `X86_64.formula` (x86-64 psABI §
   Relocation Types). Each is a subset for the loader-minimal scope:
   no static-link relocations, no TLS, no `IFUNC`, no `COPY`.

3. **Dispatch** — `formulaFor` selects the per-arch formula by
   `e_machine` (gabi 02 § ELF Identification).

These types are the *interpretive* ABI layer over `Parse.RawRela` — they
say what a relocation type code *means* (which formula to apply, what width
to write). Parse only sees `r_info` as bytes.
-/

import ElfLoader.Parse.Reloc.Raw
import ElfLoader.Parse.LoadMap.ElfHeader.Fields

-- ============================================================================
-- `r_info` bit-field accessors — unpack the packed `(sym, type)`
-- pair the formulas consume. Defined in `Parse.RawRela`'s namespace
-- for dot notation; lives here because it's interpretive.
-- ============================================================================

namespace ElfLoader.Parse.RawRela

/-- Symbol index packed into the high 32 bits of `r_info`. -/
def sym (r : RawRela) : UInt32 := (r.r_info >>> 32).toUInt32

/-- Relocation type packed into the low 32 bits of `r_info`. -/
def type (r : RawRela) : UInt32 := (r.r_info &&& 0xffffffff).toUInt32

section Example
private def r : RawRela := { r_offset := 0xdead, r_info := 0x0000007b00000403, r_addend := 0 }
#guard r.sym  = 0x7b
#guard r.type = 0x403

#guard ({ r_offset := 0, r_info := 0,    r_addend := 0 } : RawRela).sym  = 0
#guard ({ r_offset := 0, r_info := 0,    r_addend := 0 } : RawRela).type = 0
#guard ({ r_offset := 0, r_info := 1027, r_addend := 0 } : RawRela).sym  = 0
#guard ({ r_offset := 0, r_info := 1027, r_addend := 0 } : RawRela).type = 1027
end Example

end ElfLoader.Parse.RawRela

-- ============================================================================
-- Abstract relocation types — gabi 06 § Relocation.
-- ============================================================================

namespace ElfLoader.Reloc.ABI

/-- Width of a relocation write: ELF dynamic relocations write either
    a 32-bit or a 64-bit value at the target. Encoding the choice as
    a 2-element type means `Finalize.bakeReloc` dispatches
    structurally — no `if size = 8 …` runtime check, no
    width-validity lookup. Converted to `UInt8` (4 or 8) at the
    `StoreOp` boundary. -/
inductive PatchSize where | b4 | b8
  deriving Repr, BEq

/-- Inputs to a single relocation formula. Notation follows gabi 06. -/
structure FormulaInputs where
  /-- `S` — value of the resolved symbol (post base relocation). -/
  symValue : UInt64
  /-- `A` — addend (from `r_addend` for `Reloc`). -/
  addend   : UInt64
  /-- `B` — base of the object containing the relocation site. -/
  base     : UInt64
  /-- `P` — ELF address being relocated. -/
  place    : UInt64
  deriving Repr

/-- The result of applying a relocation formula. -/
structure FormulaResult where
  value : UInt64
  size  : PatchSize
  deriving Repr, BEq

/-- A relocation formula: an interpretation of `(type, inputs)`. The
    per-arch tables below instantiate this; `formulaFor` dispatches
    on `e_machine`. -/
abbrev Formula := UInt32 → FormulaInputs → Option FormulaResult

end ElfLoader.Reloc.ABI

-- ============================================================================
-- AArch64 dynamic relocations.
--
-- Spec: ARM ELF for the AArch64 ABI § Dynamic Relocations.
--
-- | Type                  | Code | Width | Formula |
-- | --------------------- | ---- | ----- | ------- |
-- | `R_AARCH64_NONE`      |    0 |   —   | none    |
-- | `R_AARCH64_ABS64`     |  257 |   8   | S + A   |
-- | `R_AARCH64_ABS32`     |  258 |   4   | S + A   |
-- | `R_AARCH64_GLOB_DAT`  | 1025 |   8   | S + A   |
-- | `R_AARCH64_JUMP_SLOT` | 1026 |   8   | S + A   |
-- | `R_AARCH64_RELATIVE`  | 1027 |   8   | B + A   |
--
-- Note: `GLOB_DAT` and `JUMP_SLOT` are documented as `S + A` for
-- completeness; in practice the linker emits them with `A = 0`.
-- ============================================================================

namespace ElfLoader.Reloc.ABI.Aarch64

open ElfLoader.Reloc.ABI

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
  else if ty == R_AARCH64_ABS64     then some { value := S + A, size := .b8 }
  else if ty == R_AARCH64_ABS32     then some { value := S + A, size := .b4 }
  else if ty == R_AARCH64_GLOB_DAT  then some { value := S + A, size := .b8 }
  else if ty == R_AARCH64_JUMP_SLOT then some { value := S + A, size := .b8 }
  else if ty == R_AARCH64_RELATIVE  then some { value := B + A, size := .b8 }
  else none

#guard (formula R_AARCH64_NONE      { symValue := 0xdead, addend := 0xbeef, base := 0xcafe, place := 0xbabe }) == none
#guard (formula 999 { symValue := 0, addend := 0, base := 0, place := 0 }) == none

#guard (formula R_AARCH64_RELATIVE { symValue := 0xdead, addend := 0xa90, base := 0x10000, place := 0 })
    == (formula R_AARCH64_RELATIVE { symValue := 0xbeef, addend := 0xa90, base := 0x10000, place := 0 })
#guard (formula R_AARCH64_RELATIVE { symValue := 0,      addend := 0xa90, base := 0x10000, place := 0 })
        == some { value := 0x10a90, size := .b8 }

#guard (formula R_AARCH64_ABS64 { symValue := 100, addend := 1, base := 0xdead, place := 0 })
    == (formula R_AARCH64_ABS64 { symValue := 100, addend := 1, base := 0xbeef, place := 0 })
#guard (formula R_AARCH64_ABS64    { symValue := 0xfeedface, addend := 0, base := 0, place := 0 })
        == some { value := 0xfeedface, size := .b8 }
#guard (formula R_AARCH64_ABS32    { symValue := 0xc0ffee,   addend := 0, base := 0, place := 0 })
        == some { value := 0xc0ffee,   size := .b4 }

#guard (formula R_AARCH64_GLOB_DAT  { symValue := 0xdeadbeef, addend := 0, base := 0, place := 0 })
        == some { value := 0xdeadbeef, size := .b8 }
#guard (formula R_AARCH64_JUMP_SLOT { symValue := 0xb16b00b5, addend := 0, base := 0, place := 0 })
        == some { value := 0xb16b00b5, size := .b8 }

#guard (formula R_AARCH64_ABS64 { symValue := 0xFFFFFFFFFFFFFFFF, addend := 1, base := 0, place := 0 })
        == some { value := 0, size := .b8 }

-- ============================================================================
-- Per-row soundness theorems. Each row of the table above has one
-- `formula_*` lemma stating its spec contract; together with
-- `formula_none_iff_unsupported` (closure), this turns the table itself
-- into the spec. A future edit that breaks any row fails at proof time.
-- ============================================================================

@[simp] theorem formula_R_AARCH64_NONE (inp : FormulaInputs) :
    formula R_AARCH64_NONE inp = none := rfl

@[simp] theorem formula_R_AARCH64_ABS64 (inp : FormulaInputs) :
    formula R_AARCH64_ABS64 inp =
      some { value := inp.symValue + inp.addend, size := .b8 } := rfl

@[simp] theorem formula_R_AARCH64_ABS32 (inp : FormulaInputs) :
    formula R_AARCH64_ABS32 inp =
      some { value := inp.symValue + inp.addend, size := .b4 } := rfl

@[simp] theorem formula_R_AARCH64_GLOB_DAT (inp : FormulaInputs) :
    formula R_AARCH64_GLOB_DAT inp =
      some { value := inp.symValue + inp.addend, size := .b8 } := rfl

@[simp] theorem formula_R_AARCH64_JUMP_SLOT (inp : FormulaInputs) :
    formula R_AARCH64_JUMP_SLOT inp =
      some { value := inp.symValue + inp.addend, size := .b8 } := rfl

@[simp] theorem formula_R_AARCH64_RELATIVE (inp : FormulaInputs) :
    formula R_AARCH64_RELATIVE inp =
      some { value := inp.base + inp.addend, size := .b8 } := rfl

/-- Closure: a successful application's type is one of the named
    codes. The contrapositive — adding a new branch to `formula`
    without naming it here breaks this proof — keeps the table
    exhaustive by construction. -/
theorem formula_some_isNamed {ty : UInt32} {inp : FormulaInputs}
    {r : FormulaResult} (h : formula ty inp = some r) :
    ty = R_AARCH64_ABS64 ∨ ty = R_AARCH64_ABS32 ∨
    ty = R_AARCH64_GLOB_DAT ∨ ty = R_AARCH64_JUMP_SLOT ∨
    ty = R_AARCH64_RELATIVE := by
  unfold formula at h
  simp only [beq_iff_eq] at h
  by_cases h0 : ty = R_AARCH64_NONE
  · rw [if_pos h0] at h; cases h
  by_cases h1 : ty = R_AARCH64_ABS64
  · exact .inl h1
  by_cases h2 : ty = R_AARCH64_ABS32
  · exact .inr (.inl h2)
  by_cases h3 : ty = R_AARCH64_GLOB_DAT
  · exact .inr (.inr (.inl h3))
  by_cases h4 : ty = R_AARCH64_JUMP_SLOT
  · exact .inr (.inr (.inr (.inl h4)))
  by_cases h5 : ty = R_AARCH64_RELATIVE
  · exact .inr (.inr (.inr (.inr h5)))
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5] at h
  cases h

end ElfLoader.Reloc.ABI.Aarch64

-- ============================================================================
-- x86-64 dynamic relocations.
--
-- Spec: x86-64 psABI § Relocation Types
-- (`third_party/abi/x86-64-abi/x86-64-ABI/object-files.tex`, table
-- `tab-relocations`).
--
-- | Type                  | Code | Width | Formula |
-- | --------------------- | ---- | ----- | ------- |
-- | `R_X86_64_NONE`       |    0 |   —   | none    |
-- | `R_X86_64_64`         |    1 |   8   | S + A   |
-- | `R_X86_64_GLOB_DAT`   |    6 |   8   | S       |
-- | `R_X86_64_JUMP_SLOT`  |    7 |   8   | S       |
-- | `R_X86_64_RELATIVE`   |    8 |   8   | B + A   |
-- | `R_X86_64_32`         |   10 |   4   | S + A   |
--
-- `GLOB_DAT` / `JUMP_SLOT` are `S` per the psABI table — no addend.
-- (AArch64 documents them as `S + A`; the addend is conventionally 0
-- in both cases, but we follow each arch's spec literally.)
--
-- `R_X86_64_32` truncates to 32 bits.
-- ============================================================================

namespace ElfLoader.Reloc.ABI.X86_64

open ElfLoader.Reloc.ABI

def R_X86_64_NONE      : UInt32 := 0
def R_X86_64_64        : UInt32 := 1
def R_X86_64_GLOB_DAT  : UInt32 := 6
def R_X86_64_JUMP_SLOT : UInt32 := 7
def R_X86_64_RELATIVE  : UInt32 := 8
def R_X86_64_32        : UInt32 := 10

/-- Apply an x86-64 dynamic-relocation formula. Returns `none` for
    `R_X86_64_NONE` and any unsupported type. -/
def formula : Formula := fun ty inp =>
  let S := inp.symValue
  let A := inp.addend
  let B := inp.base
  if ty == R_X86_64_NONE       then none
  else if ty == R_X86_64_64        then some { value := S + A, size := .b8 }
  else if ty == R_X86_64_GLOB_DAT  then some { value := S,     size := .b8 }
  else if ty == R_X86_64_JUMP_SLOT then some { value := S,     size := .b8 }
  else if ty == R_X86_64_RELATIVE  then some { value := B + A, size := .b8 }
  else if ty == R_X86_64_32        then some { value := S + A, size := .b4 }
  else none

#guard (formula R_X86_64_NONE  { symValue := 0xdead, addend := 0xbeef, base := 0xcafe, place := 0xbabe }) == none
#guard (formula 999 { symValue := 0, addend := 0, base := 0, place := 0 }) == none

#guard (formula R_X86_64_RELATIVE { symValue := 0xdead, addend := 0xa90, base := 0x10000, place := 0 })
    == (formula R_X86_64_RELATIVE { symValue := 0xbeef, addend := 0xa90, base := 0x10000, place := 0 })
#guard (formula R_X86_64_RELATIVE { symValue := 0,      addend := 0xa90, base := 0x10000, place := 0 })
        == some { value := 0x10a90, size := .b8 }

#guard (formula R_X86_64_64 { symValue := 100, addend := 1, base := 0xdead, place := 0 })
    == (formula R_X86_64_64 { symValue := 100, addend := 1, base := 0xbeef, place := 0 })
#guard (formula R_X86_64_64 { symValue := 0xfeedface, addend := 0, base := 0, place := 0 })
        == some { value := 0xfeedface, size := .b8 }
#guard (formula R_X86_64_32 { symValue := 0xc0ffee,   addend := 0, base := 0, place := 0 })
        == some { value := 0xc0ffee,   size := .b4 }

#guard (formula R_X86_64_GLOB_DAT  { symValue := 0xdeadbeef, addend := 0xbad, base := 0, place := 0 })
        == some { value := 0xdeadbeef, size := .b8 }
#guard (formula R_X86_64_JUMP_SLOT { symValue := 0xb16b00b5, addend := 0xbad, base := 0, place := 0 })
        == some { value := 0xb16b00b5, size := .b8 }

#guard (formula R_X86_64_64 { symValue := 0xFFFFFFFFFFFFFFFF, addend := 1, base := 0, place := 0 })
        == some { value := 0, size := .b8 }

-- ============================================================================
-- Per-row soundness theorems. Mirrors the AArch64 block above; each row
-- of the table has one `formula_*` lemma stating its spec contract.
-- Note `GLOB_DAT` / `JUMP_SLOT` are `S` (no addend) per x86-64 psABI —
-- different from AArch64's `S + A`.
-- ============================================================================

@[simp] theorem formula_R_X86_64_NONE (inp : FormulaInputs) :
    formula R_X86_64_NONE inp = none := rfl

@[simp] theorem formula_R_X86_64_64 (inp : FormulaInputs) :
    formula R_X86_64_64 inp =
      some { value := inp.symValue + inp.addend, size := .b8 } := rfl

@[simp] theorem formula_R_X86_64_GLOB_DAT (inp : FormulaInputs) :
    formula R_X86_64_GLOB_DAT inp =
      some { value := inp.symValue, size := .b8 } := rfl

@[simp] theorem formula_R_X86_64_JUMP_SLOT (inp : FormulaInputs) :
    formula R_X86_64_JUMP_SLOT inp =
      some { value := inp.symValue, size := .b8 } := rfl

@[simp] theorem formula_R_X86_64_RELATIVE (inp : FormulaInputs) :
    formula R_X86_64_RELATIVE inp =
      some { value := inp.base + inp.addend, size := .b8 } := rfl

@[simp] theorem formula_R_X86_64_32 (inp : FormulaInputs) :
    formula R_X86_64_32 inp =
      some { value := inp.symValue + inp.addend, size := .b4 } := rfl

/-- Closure: a successful application's type is one of the named codes. -/
theorem formula_some_isNamed {ty : UInt32} {inp : FormulaInputs}
    {r : FormulaResult} (h : formula ty inp = some r) :
    ty = R_X86_64_64 ∨ ty = R_X86_64_GLOB_DAT ∨ ty = R_X86_64_JUMP_SLOT ∨
    ty = R_X86_64_RELATIVE ∨ ty = R_X86_64_32 := by
  unfold formula at h
  simp only [beq_iff_eq] at h
  by_cases h0 : ty = R_X86_64_NONE
  · rw [if_pos h0] at h; cases h
  by_cases h1 : ty = R_X86_64_64
  · exact .inl h1
  by_cases h2 : ty = R_X86_64_GLOB_DAT
  · exact .inr (.inl h2)
  by_cases h3 : ty = R_X86_64_JUMP_SLOT
  · exact .inr (.inr (.inl h3))
  by_cases h4 : ty = R_X86_64_RELATIVE
  · exact .inr (.inr (.inr (.inl h4)))
  by_cases h5 : ty = R_X86_64_32
  · exact .inr (.inr (.inr (.inr h5)))
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5] at h
  cases h

end ElfLoader.Reloc.ABI.X86_64

-- ============================================================================
-- Per-`e_machine` dispatch.
-- ============================================================================

namespace ElfLoader.Reloc.ABI

/-- Pick the relocation formula for `machine`. -/
def formulaFor : ElfLoader.Parse.ElfMachine → Formula
  | .aarch64 => Aarch64.formula
  | .x86_64  => X86_64.formula

end ElfLoader.Reloc.ABI

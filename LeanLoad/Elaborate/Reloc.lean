/-
Relocation formula types — gabi-06 abstract `(S, A, B, P)` inputs
and the per-arch dispatch surface.

Spec: gabi 06 (`third_party/gabi/docsrc/elf/06-reloc.rst`).
Per-arch tables (`R_AARCH64_*`, `R_X86_64_*`) live in
`Elaborate/Reloc/{Aarch64, X86_64}.lean`; per-`e_machine` dispatch
in `Elaborate/Reloc/Formula.lean`.

These types are the *interpretive* layer over `Parse.RawRela` —
they say what a relocation type code *means* (which formula to
apply, what width to write). Parse only sees `r_info` as bytes.
-/

import LeanLoad.Parse.Reloc

namespace LeanLoad.Elaborate

/-- Width of a relocation write: ELF dynamic relocations write either
    a 32-bit or a 64-bit value at the target. Encoding the choice as
    a 2-element type means `Exec.applyPatch` dispatches structurally —
    no `if size = 8 ...` runtime check, no width-validity lookup. -/
inductive PatchSize where | b4 | b8
  deriving Repr, BEq

/-- Width as a `Nat`, for diagnostics / `inRange` arithmetic. -/
def PatchSize.toNat : PatchSize → Nat
  | .b4 => 4
  | .b8 => 8

/-- Inputs to a single relocation formula. Notation follows gabi 06. -/
structure FormulaInputs where
  /-- `S` — value of the resolved symbol (post base relocation). -/
  symValue : UInt64
  /-- `A` — addend (from `r_addend` for `Rela`). -/
  addend   : UInt64
  /-- `B` — base of the object containing the relocation site. -/
  base     : UInt64
  /-- `P` — virtual address being relocated. -/
  place    : UInt64
  deriving Repr

/-- The result of applying a relocation formula. -/
structure FormulaResult where
  value : UInt64
  size  : PatchSize
  deriving Repr, BEq

/-- A relocation formula: an interpretation of `(type, inputs)`. The
    per-arch tables in `Elaborate/Reloc/{Aarch64,X86_64}.lean`
    instantiate this; `Elaborate/Reloc/Formula.lean` dispatches on
    `e_machine`. -/
abbrev Formula := UInt32 → FormulaInputs → Option FormulaResult

end LeanLoad.Elaborate

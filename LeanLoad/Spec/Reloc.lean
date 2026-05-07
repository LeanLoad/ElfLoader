/-
Relocation entries — gabi 06 spec.

Spec: gabi 06 (`third_party/gabi/docsrc/elf/06-reloc.rst`).
Architecture-specific relocation types and formula tables
(`R_AARCH64_*` in `Spec/Reloc/Aarch64.lean`, `R_X86_64_*` in
`Spec/Reloc/X86_64.lean`) live under `Spec/Reloc/`. The pure planner
that turns parsed `Rela`s into a list of `Patch`es is
`LeanLoad.Plan.Reloc`.

`Elf64_Rela` packs symbol index and relocation type into `r_info`:

    sym  = r_info >> 32
    type = r_info & 0xffffffff

We model only `Rela` (with addend); the `Rel` form is allowed by gabi
but neither AArch64 nor x86-64 emits it for dynamic relocations, so
the parser path is omitted until a fixture demands it.

# Formula types

`PatchSize`, `FormulaInputs`, `FormulaResult`, `Formula` capture the
gabi-06 abstract relocation formula (S, A, B, P inputs → value+width
output). They live here, alongside `Rela64`, so per-arch formula
tables (`Spec/Reloc/{Aarch64,X86_64}.lean`) can define formulas
without depending on the planner. The planner (`LeanLoad.Plan.Reloc`)
imports these types in turn.
-/

namespace LeanLoad.Spec.Reloc

/-- 64-bit relocation entry with explicit addend. `r_addend` is stored
    as `UInt64` here; per gabi 06 it is the bit pattern of an
    `Elf64_Sxword` (signed). The signed interpretation happens at
    application time. -/
structure Rela64 where
  r_offset : UInt64
  r_info   : UInt64
  r_addend : UInt64
  deriving Repr, Inhabited

/-- Size of one `Elf64_Rela` on disk (gabi 06: 8+8+8 = 24). -/
def Rela64.entrySize : Nat := 24

def Rela64.sym (r : Rela64) : UInt32 := (r.r_info >>> 32).toUInt32
def Rela64.type (r : Rela64) : UInt32 := (r.r_info &&& 0xffffffff).toUInt32

section Example
-- `r_info` packs sym (high 32) + type (low 32). Spot-check both halves.
private def r : Rela64 := { r_offset := 0xdead, r_info := 0x0000007b00000403, r_addend := 0 }
#guard r.sym  = 0x7b      -- decimal 123
#guard r.type = 0x403     -- decimal 1027 (R_AARCH64_RELATIVE)

-- Edges: sym=0 (no symbol, RELATIVE-style), type=0 (R_*_NONE).
#guard ({ r_offset := 0, r_info := 0, r_addend := 0 } : Rela64).sym  = 0
#guard ({ r_offset := 0, r_info := 0, r_addend := 0 } : Rela64).type = 0
-- Pure type-only encoding (RELATIVE on AArch64): info = 1027.
#guard ({ r_offset := 0, r_info := 1027, r_addend := 0 } : Rela64).sym  = 0
#guard ({ r_offset := 0, r_info := 1027, r_addend := 0 } : Rela64).type = 1027
end Example

-- ============================================================================
-- Relocation formula — gabi 06 abstract S/A/B/P inputs.
-- ============================================================================

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
    per-arch tables in `Spec/Reloc/{Aarch64,X86_64}.lean` instantiate
    this; `Spec/Reloc/Formula.lean` dispatches on `e_machine`. -/
abbrev Formula := UInt32 → FormulaInputs → Option FormulaResult

end LeanLoad.Spec.Reloc

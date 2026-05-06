/-
Relocation entries — gabi 06 spec.

Spec: gabi 06 (`third_party/gabi/docsrc/elf/06-reloc.rst`).
Architecture-specific relocation types and formula tables
(`R_AARCH64_*` in `Spec/Reloc/Aarch64.lean`, `R_X86_64_*` in
`Spec/Reloc/X86_64.lean`) live under `Spec/Reloc/`. The pure planner
that turns parsed `Rela`s into a list of `Patch`es is
`LeanLoad.Reloc`.

`Elf64_Rela` packs symbol index and relocation type into `r_info`:

    sym  = r_info >> 32
    type = r_info & 0xffffffff

We model only `Rela` (with addend); the `Rel` form is allowed by gabi
but neither AArch64 nor x86-64 emits it for dynamic relocations, so
the parser path is omitted until a fixture demands it.
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

section UnitTest
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
end UnitTest

end LeanLoad.Spec.Reloc

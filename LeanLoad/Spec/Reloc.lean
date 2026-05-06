/-
Relocation entries — gabi 06 spec.

Spec: gabi 06 (`third_party/gabi/docsrc/elf/06-reloc.rst`).
Architecture-specific relocation types and formula tables
(`R_AARCH64_*` in `Spec/Reloc/Aarch64.lean`, `R_X86_64_*` in
`Spec/Reloc/X86_64.lean`) live under `Spec/Reloc/`. The pure planner
that turns parsed `Rela`s into a list of `RelocWrite`s is
`LeanLoad.Reloc`.

For ELF64, both `Elf64_Rel` and `Elf64_Rela` pack symbol index and
relocation type into `r_info`:

    sym  = r_info >> 32
    type = r_info & 0xffffffff
-/

namespace LeanLoad.Spec.Reloc

-- ============================================================================
-- Rel — gabi 06 (Elf64_Rel)
-- ============================================================================

/-- 64-bit relocation entry without addend. -/
structure Rel64 where
  r_offset : UInt64
  r_info   : UInt64
  deriving Repr, Inhabited

/-- Size of one `Elf64_Rel` on disk (gabi 06: 8+8 = 16). -/
def Rel64.entrySize : Nat := 16

/-- Symbol-table index from `r_info` (high 32 bits on ELF64). -/
def Rel64.sym (r : Rel64) : UInt32 := (r.r_info >>> 32).toUInt32

/-- Relocation type from `r_info` (low 32 bits on ELF64). -/
def Rel64.type (r : Rel64) : UInt32 := (r.r_info &&& 0xffffffff).toUInt32

-- ============================================================================
-- Rela — gabi 06 (Elf64_Rela)
-- ============================================================================

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

#guard Rel64.entrySize = 16
#guard Rela64.entrySize = 24

end LeanLoad.Spec.Reloc

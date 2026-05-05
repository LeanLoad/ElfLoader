/-
Relocation entries.

Spec: gabi 06 (`third_party/gabi/docsrc/elf/06-reloc.rst`).
Architecture-specific relocation types (`R_X86_64_*` etc.) and the
formulas applied to them live in `LeanLoad.Link.Reloc`; this file only
parses the on-disk structures.

For ELF64, both `Elf64_Rel` and `Elf64_Rela` pack symbol index and
relocation type into `r_info`:

    sym  = r_info >> 32
    type = r_info & 0xffffffff
-/

import LeanLoad.Parse.Bytes

namespace LeanLoad.Parse.Reloc

open LeanLoad.Parse
open LeanLoad.Parse.Bytes

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

def parseRel : Parser Rel64 := do
  let r_offset ← u64le
  let r_info   ← u64le
  return { r_offset, r_info }

-- ============================================================================
-- Rela — gabi 06 (Elf64_Rela)
-- ============================================================================

/-- 64-bit relocation entry with explicit addend. `r_addend` is stored
    as `UInt64` here; per gabi 06 it is the bit pattern of an
    `Elf64_Sxword` (signed). The signed interpretation happens at
    application time in `Link.Reloc`. -/
structure Rela64 where
  r_offset : UInt64
  r_info   : UInt64
  r_addend : UInt64
  deriving Repr, Inhabited

/-- Size of one `Elf64_Rela` on disk (gabi 06: 8+8+8 = 24). -/
def Rela64.entrySize : Nat := 24

def Rela64.sym (r : Rela64) : UInt32 := (r.r_info >>> 32).toUInt32
def Rela64.type (r : Rela64) : UInt32 := (r.r_info &&& 0xffffffff).toUInt32

def parseRela : Parser Rela64 := do
  let r_offset ← u64le
  let r_info   ← u64le
  let r_addend ← u64le
  return { r_offset, r_info, r_addend }

#guard Rel64.entrySize = 16
#guard Rela64.entrySize = 24

-- ============================================================================
-- Tables
-- ============================================================================

/-- Parse `count` `Elf64_Rel` entries starting at `offset`. -/
def parseRelTable (offset count : Nat) : Parser (Array Rel64) :=
  parseArray offset count parseRel

/-- Parse `count` `Elf64_Rela` entries starting at `offset`. -/
def parseRelaTable (offset count : Nat) : Parser (Array Rela64) :=
  parseArray offset count parseRela

end LeanLoad.Parse.Reloc

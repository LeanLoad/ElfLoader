/-
Dynamic symbol table — bytes only.

Spec: gabi 05 (`third_party/gabi/docsrc/elf/05-symtab.rst`) § Symbol Table.

Type + byte-level parser. Semantic interpretation of `st_info`
(STB_*, STT_*) and the reserved `st_shndx` values (SHN_UNDEF / ABS /
COMMON) is `Elaborate`'s job — they're enums there.
-/

import LeanLoad.Parse.Bytes

namespace LeanLoad.Parse

/-- Raw 64-bit symbol entry — gabi 05 (Elf64_Sym). Field layout
    matches `Elf64_Sym`; semantic decomposition of `st_info` and
    interpretation of `st_shndx` reserved values happen in
    `Elaborate`. -/
structure RawSym where
  st_name  : UInt32   -- string table offset
  st_info  : UInt8    -- bind << 4 | type
  st_other : UInt8    -- visibility
  st_shndx : UInt16   -- section index (or `SHN_*` reserved value)
  st_value : UInt64
  st_size  : UInt64
  deriving Repr, Inhabited

namespace RawSym

/-- Size of one entry on disk (gabi 05: 4+1+1+2+8+8 = 24). -/
def entrySize : Nat := 24

/-- Symbol binding (high nibble of `st_info`). gabi 05 § Symbol Table. -/
def bind (s : RawSym) : UInt8 := s.st_info >>> 4

/-- Symbol type (low nibble of `st_info`). gabi 05 § Symbol Table. -/
def type (s : RawSym) : UInt8 := s.st_info &&& 0xf

end RawSym

end LeanLoad.Parse

-- ============================================================================
-- Byte-level parser.
-- ============================================================================

namespace LeanLoad.Parse.Symbol

open LeanLoad.Parse
open LeanLoad.Parse.Bytes

/-- Parse one symbol entry at the current cursor. -/
def parse : Parser RawSym := do
  let st_name  ← u32le
  let st_info  ← u8
  let st_other ← u8
  let st_shndx ← u16le
  let st_value ← u64le
  let st_size  ← u64le
  return { st_name, st_info, st_other, st_shndx, st_value, st_size }

/-- Parse `count` consecutive symbol entries starting at `offset`. -/
def parseTable (offset count : Nat) : Parser (Array RawSym) :=
  parseArray offset count parse

end LeanLoad.Parse.Symbol

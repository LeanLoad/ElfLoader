/-
String table and dynamic symbol table.

Specs:
- gabi 04 (`third_party/gabi/docsrc/elf/04-strtab.rst`) — string tables.
- gabi 05 (`third_party/gabi/docsrc/elf/05-symtab.rst`) — symbol tables.

The dynamic linker reaches both via the `.dynamic` array (`DT_STRTAB`,
`DT_STRSZ`, `DT_SYMTAB`, `DT_SYMENT`).
-/

import LeanLoad.Parse.Bytes

namespace LeanLoad.Parse.Symbol

open LeanLoad.Parse
open LeanLoad.Parse.Bytes

-- ============================================================================
-- Constants — gabi 05 Tables: Symbol Binding, Symbol Types, Section Index
-- ============================================================================

-- st_info high nibble (binding)
def STB_LOCAL  : UInt8 := 0
def STB_GLOBAL : UInt8 := 1
def STB_WEAK   : UInt8 := 2

-- st_info low nibble (type)
def STT_NOTYPE  : UInt8 := 0
def STT_OBJECT  : UInt8 := 1
def STT_FUNC    : UInt8 := 2
def STT_SECTION : UInt8 := 3
def STT_FILE    : UInt8 := 4
def STT_COMMON  : UInt8 := 5
def STT_TLS     : UInt8 := 6

-- Reserved section indices
def SHN_UNDEF  : UInt16 := 0
def SHN_ABS    : UInt16 := 0xfff1
def SHN_COMMON : UInt16 := 0xfff2

#guard STB_GLOBAL = 1
#guard STT_FUNC = 2
#guard SHN_UNDEF = 0

-- ============================================================================
-- Symbol entry — gabi 05 (Elf64_Sym)
-- ============================================================================

/-- 64-bit symbol entry. Field layout matches `Elf64_Sym` in gabi 05. -/
structure Symbol64 where
  st_name  : UInt32   -- string table offset
  st_info  : UInt8    -- bind << 4 | type
  st_other : UInt8    -- visibility
  st_shndx : UInt16   -- section index (or `SHN_*`)
  st_value : UInt64
  st_size  : UInt64
  deriving Repr, Inhabited

/-- Size of one entry on disk (gabi 05: 4+1+1+2+8+8 = 24). -/
def entrySize : Nat := 24

#guard entrySize = 24

/-- Symbol binding (high nibble of `st_info`). -/
def Symbol64.bind (s : Symbol64) : UInt8 := s.st_info >>> 4

/-- Symbol type (low nibble of `st_info`). -/
def Symbol64.type (s : Symbol64) : UInt8 := s.st_info &&& 0xf

/-- Parse one symbol entry at the current cursor. -/
def parse : Parser Symbol64 := do
  let st_name  ← u32le
  let st_info  ← u8
  let st_other ← u8
  let st_shndx ← u16le
  let st_value ← u64le
  let st_size  ← u64le
  return { st_name, st_info, st_other, st_shndx, st_value, st_size }

/-- Parse `count` consecutive symbol entries starting at `offset`. -/
def parseTable (offset count : Nat) : Parser (Array Symbol64) :=
  parseArray offset count parse

-- ============================================================================
-- String table — gabi 04
-- ============================================================================

/-- A string table is just a byte buffer; entries are null-terminated
    C strings indexed by `st_name`. -/
abbrev StringTable := ByteArray

/-- Read the null-terminated string at `offset` in `tab`. Returns
    `none` if `offset` is past the end. The result excludes the null. -/
def StringTable.lookup (tab : StringTable) (offset : Nat) : Option String :=
  if offset >= tab.size then
    none
  else
    let endIdx := tab.findIdx? (· == 0) offset |>.getD tab.size
    String.fromUTF8? (tab.extract offset endIdx)

/-- Read a string table out of the file: `offset .. offset+size`. -/
def parseStringTable (offset size : Nat) : Parser StringTable := do
  seek offset
  slice size

end LeanLoad.Parse.Symbol

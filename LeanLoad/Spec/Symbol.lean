/-
Dynamic symbol table — gabi 05 spec.

Spec: gabi 05 (`third_party/gabi/docsrc/elf/05-symtab.rst`) § Symbol Table.

The dynamic linker reaches the symbol table via `DT_SYMTAB` /
`DT_SYMENT` in the `.dynamic` array. String-table types live in
`LeanLoad.Spec.StringTable` (gabi 04).

Types and constants only — parser in `LeanLoad.Parse.Symbol`.
-/

namespace LeanLoad.Spec.Symbol

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

/-- Symbol binding (high nibble of `st_info`). gabi 05 § Symbol Table. -/
def Symbol64.bind (s : Symbol64) : UInt8 := s.st_info >>> 4

/-- Symbol type (low nibble of `st_info`). gabi 05 § Symbol Table. -/
def Symbol64.type (s : Symbol64) : UInt8 := s.st_info &&& 0xf

section UnitTest
-- `st_info = bind << 4 | type`. Spot-check both halves on a few
-- canonical encodings.
private def mk (st_info : UInt8) : Symbol64 :=
  { (default : Symbol64) with st_info }

-- STB_GLOBAL (1) | STT_FUNC (2) → 0x12.
#guard (mk 0x12).bind = STB_GLOBAL
#guard (mk 0x12).type = STT_FUNC
-- STB_WEAK (2) | STT_OBJECT (1) → 0x21.
#guard (mk 0x21).bind = STB_WEAK
#guard (mk 0x21).type = STT_OBJECT
-- STB_LOCAL (0) | STT_NOTYPE (0) → 0x00.
#guard (mk 0x00).bind = STB_LOCAL
#guard (mk 0x00).type = STT_NOTYPE
end UnitTest

end LeanLoad.Spec.Symbol

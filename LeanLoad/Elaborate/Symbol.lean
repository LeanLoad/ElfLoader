/-
Symbol-table elaboration: gabi-05 binding/type/section-index
constants, `RawSym` classification predicates, and the per-symbol
`Symbol` bundle (a `RawSym` paired with its pre-resolved name).

Spec: gabi 05 (`third_party/gabi/docsrc/elf/05-symtab.rst`) § Symbol
Table.

The classification predicates (`isGlobalDef`, `isUndef`, `isWeak`) are
defined in `Parse.RawSym`'s namespace for dot notation but live here
because they're semantic interpretations of `st_info` and `st_shndx`
— Parse only sees the bit-fields as bytes.
-/

import LeanLoad.Parse.Structs

-- ============================================================================
-- gabi-05 constants.
-- ============================================================================

namespace LeanLoad.Elaborate

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

end LeanLoad.Elaborate

-- ============================================================================
-- RawSym predicates — semantic reading of `st_info` / `st_shndx`.
-- ============================================================================

namespace LeanLoad.Parse.RawSym

open LeanLoad.Elaborate (STB_LOCAL STB_WEAK SHN_UNDEF)

/-- Symbol binding (high nibble of `st_info`). gabi 05 § Symbol Table. -/
def bind (s : RawSym) : UInt8 := s.st_info >>> 4

/-- True iff `sym` is an externally-visible definition. -/
def isGlobalDef (s : RawSym) : Bool :=
  s.st_shndx != SHN_UNDEF && s.bind != STB_LOCAL

/-- True iff `sym` is an undefined reference. -/
def isUndef (s : RawSym) : Bool :=
  s.st_shndx == SHN_UNDEF

/-- True iff `sym` is weak (gabi 05): a weak undefined reference is
    allowed to remain unresolved at link time. -/
def isWeak (s : RawSym) : Bool :=
  s.bind == STB_WEAK

end LeanLoad.Parse.RawSym

-- ============================================================================
-- Per-symbol bundle: a `RawSym` paired with its pre-resolved name.
-- ============================================================================

namespace LeanLoad.Elaborate

open LeanLoad.Parse (RawSym)

/-- A `RawSym` plus its pre-resolved name. `none` if the entry's
    `st_name` offset doesn't point into the string table. -/
structure Symbol where
  sym  : RawSym
  name : Option String
  deriving Inhabited

end LeanLoad.Elaborate

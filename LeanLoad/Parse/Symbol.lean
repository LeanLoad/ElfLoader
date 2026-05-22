/-
Symbol-table checking: typed views over `st_info` (binding) and
`st_shndx` (section index), and the per-symbol `Symbol` bundle that
post-parse code consumes.

Spec: gabi 05 (`third_party/gabi/docsrc/elf/05-symtab.rst`) § Symbol
Table.

Where `Parse.RawSym` carries the raw byte-fields, `Symbol` carries
the *meaning*: `bind : SymBind`, `shndx : ShnIdx`, plus the resolved
name and `value`. The closed `SymBind` enum rejects OS- or processor-
specific extensions during checking; `ShnIdx.concrete` covers the open
range of legitimate section indices.

The low nibble of `st_info` (the symbol-type field) and `st_size` are
not lifted — no consumer reads them.
-/

import LeanLoad.Parse.Dynamic.RawSym
import LeanLoad.Parse.Dynamic.RawStrtab

namespace LeanLoad.Parse

-- ============================================================================
-- Typed views: each enum paired with its `ofRaw` lift.
-- ============================================================================

/-- Symbol binding (gabi 05): the high nibble of `st_info`. -/
inductive SymBind where
  | local
  | global
  | weak
  deriving Repr, BEq, Inhabited

/-- Lift the high nibble of `st_info`. `none` for OS- or processor-
    specific bindings (`STB_LOOS`–`STB_HIPROC`); `Symbol.ofRaw` rejects. -/
def SymBind.ofRaw : UInt8 → Option SymBind
  | 0 => some .local
  | 1 => some .global
  | 2 => some .weak
  | _ => Option.none

#guard SymBind.ofRaw 1 == some .global
#guard SymBind.ofRaw 99 == none

/-- Section-header index in a symbol entry (gabi 05). The reserved
    indices (`SHN_UNDEF`, `SHN_ABS`, `SHN_COMMON`) get named cases;
    a concrete in-file section is `concrete n`. -/
inductive ShnIdx where
  | undef
  | abs
  | common
  | concrete (n : UInt16)
  deriving Repr, BEq, Inhabited

/-- Lift `st_shndx`. Total: any non-reserved value is a `concrete`
    section index. -/
def ShnIdx.ofRaw : UInt16 → ShnIdx
  | 0      => .undef
  | 0xfff1 => .abs
  | 0xfff2 => .common
  | n      => .concrete n

#guard ShnIdx.ofRaw 0 == .undef
#guard ShnIdx.ofRaw 0xfff1 == .abs
#guard ShnIdx.ofRaw 5 == .concrete 5

-- ============================================================================
-- Per-symbol bundle. Replaces the raw `RawSym` view after checking.
-- ============================================================================

/-- A checked symbol. Raw `st_*` byte-fields lifted into
    typed views; `name` pre-resolved against the dynamic string table
    (`none` if `st_name` was out of range or didn't decode as UTF-8). -/
structure Symbol where
  name  : Option String
  bind  : SymBind
  shndx : ShnIdx
  /-- `st_value` — for in-memory symbols, the section-relative VA. -/
  value : UInt64
  deriving Repr, Inhabited

namespace Symbol

/-- True iff `s` is an externally-visible definition: it lives in a
    real section (`shndx ≠ undef`) and isn't local. LeanLoad-specific
    composite — gabi names the constituent parts (gabi 05 § Symbol
    Table: `st_shndx`, `STB_LOCAL`) but doesn't define this exact
    predicate; it's the conventional shape used by ld/ld.so. -/
def isGlobalDef (s : Symbol) : Bool :=
  match s.shndx, s.bind with
  | .undef, _ => false
  | _, .local => false
  | _, _      => true

/-- True iff `s` is an undefined reference (`shndx = undef`). -/
def isUndef (s : Symbol) : Bool :=
  match s.shndx with
  | .undef => true
  | _      => false

/-- True iff `s` is weak (gabi 05): a weak undefined reference is
    allowed to remain unresolved at link time. -/
def isWeak (s : Symbol) : Bool :=
  match s.bind with
  | .weak => true
  | _     => false

end Symbol

-- ============================================================================
-- Build a `Symbol` from a `RawSym` plus the dynamic string table.
-- Fails with a typed error on unknown bind bits.
-- ============================================================================

/-- Build a `Symbol` from a `RawSym` by lifting `st_info`'s binding
    nibble to `SymBind` and resolving `st_name` against `strtab`.
    Fails if the binding nibble is not in the gabi-05 named set. -/
def Symbol.ofRaw (strtab : RawStrtab) (s : RawSym) : Except String Symbol := do
  let bindRaw := s.st_info >>> 4
  let some bind := SymBind.ofRaw bindRaw
    | .error s!"unknown st_info binding={bindRaw}"
  -- `st_name` is a UInt32 strtab offset; wrap it at this boundary.
  return { name  := strtab.lookup ⟨s.st_name.toUInt64⟩
           bind
           shndx := ShnIdx.ofRaw s.st_shndx
           value := s.st_value }

end LeanLoad.Parse

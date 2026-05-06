/-
Symbol resolution.

Spec: gabi 08 § Shared Object Dependencies — "When resolving symbolic
references, the dynamic linker examines the symbol tables with a
breadth-first search. That is, it first looks at the symbol table of
the executable program itself, then at the symbol tables of the
`DT_NEEDED` entries (in order), and then at the second level
`DT_NEEDED` entries, and so on."

An object's symbol is a *definition* if `st_shndx ≠ SHN_UNDEF` and is
not `STB_LOCAL`. An *undefined reference* has `st_shndx = SHN_UNDEF`.
For each undefined reference across all loaded objects, we find a
defining (object, symbol) pair via breadth-first search over the
`DepGraph.objects` array (which `Discover` already returns in BFS
order: main first, then NEEDED entries in their declared order).
-/

import LeanLoad.DiscoverPlan
import LeanLoad.Spec.Symbol
import LeanLoad.Fixtures

namespace LeanLoad.Resolve

open LeanLoad.Spec

open LeanLoad
open LeanLoad.Discover

/-- A resolved global symbol: its providing object's index in the
    `DepGraph.objects` array and the symbol's index within that
    object's `symtab`. -/
structure SymRef where
  objectIdx : Nat
  symIdx    : Nat
  deriving Repr

/-- True iff `sym` is an externally-visible definition. -/
def isGlobalDef (sym : Symbol.Symbol64) : Bool :=
  sym.st_shndx != Symbol.SHN_UNDEF && sym.bind != Symbol.STB_LOCAL

/-- True iff `sym` is an undefined reference. -/
def isUndef (sym : Symbol.Symbol64) : Bool :=
  sym.st_shndx == Symbol.SHN_UNDEF

/-- True iff `sym` is weak (gabi 05): a weak undefined reference is
    allowed to remain unresolved at link time. -/
def isWeak (sym : Symbol.Symbol64) : Bool :=
  sym.bind == Symbol.STB_WEAK

/-- Symbol name from an object's strtab. -/
def symName (obj : Discover.LoadedObject) (sym : Symbol.Symbol64) : Option String :=
  Spec.StringTable.lookup obj.elf.strtab sym.st_name.toNat

/-- Look up `name` as a global definition in `obj`'s symbol table. -/
def findInObject (obj : Discover.LoadedObject) (name : String) : Option Nat :=
  obj.elf.symtab.findIdx? fun sym =>
    isGlobalDef sym && symName obj sym == some name

/-- Resolve `name` against `g` via breadth-first search over its
    objects. Returns the providing `SymRef`, or `none` if no object
    defines it. -/
def resolveByName (g : DepGraph) (name : String) : Option SymRef := Id.run do
  let mut idx := 0
  for obj in g.objects do
    if let some symIdx := findInObject obj name then
      return some { objectIdx := idx, symIdx }
    idx := idx + 1
  return none

/-- A failed-to-resolve undefined symbol; useful for diagnostics. -/
structure Unresolved where
  objectIdx : Nat
  symIdx    : Nat
  name      : String
  deriving Repr

/-- Result of building the resolution table for an entire
    `DepGraph`. -/
structure Table where
  /-- One entry per undefined reference in any object. -/
  resolved : Array (Unresolved × Option SymRef)
  /-- Strong (non-weak) undef references that did not resolve.
      A non-empty `missing` means the program would fail at load. -/
  missing  : Array Unresolved
  /-- Weak undef references that did not resolve. Allowed by gabi 05;
      surfaced for diagnostics only. -/
  weakMissing : Array Unresolved
  deriving Repr

/-- Walk every object's symbol table, look up each undefined
    reference's definition. -/
def buildTable (g : DepGraph) : Table := Id.run do
  let mut resolved : Array (Unresolved × Option SymRef) := #[]
  let mut missing : Array Unresolved := #[]
  let mut weakMissing : Array Unresolved := #[]
  let mut objIdx := 0
  for obj in g.objects do
    let mut symIdx := 0
    for sym in obj.elf.symtab do
      if isUndef sym then
        match symName obj sym with
        | none    => pure ()
        | some "" => pure ()
        | some n =>
          let entry : Unresolved := { objectIdx := objIdx, symIdx, name := n }
          let r := resolveByName g n
          resolved := resolved.push (entry, r)
          if r.isNone then
            if isWeak sym then weakMissing := weakMissing.push entry
            else missing := missing.push entry
      symIdx := symIdx + 1
    objIdx := objIdx + 1
  return { resolved, missing, weakMissing }

-- ============================================================================
-- Compile-time unit tests: synthesise a tiny `DepGraph` where main has an
-- undefined ref to `printf` and libc defines it, then check the
-- resolver finds the right pair.
-- ============================================================================
section UnitTest
open LeanLoad.Fixtures

/-- Pack `ss` into a NUL-separated `.dynstr`; offset 0 reserved for "". -/
private def packStrings (ss : Array String) : Spec.StringTable.StringTable × Array Nat :=
  let init : ByteArray × Array Nat := (⟨#[0]⟩, #[])
  let (acc, offs) := ss.foldl (init := init) fun (a, os) s =>
    let off := a.size
    let bs  := s.toUTF8
    (a ++ bs ++ ⟨#[0]⟩, os.push off)
  (acc, offs)

private def defSym (nameOff : UInt32) (value : UInt64) : Symbol.Symbol64 :=
  { (default : Symbol.Symbol64) with
    st_name := nameOff, st_info := (1 : UInt8) <<< 4
    st_shndx := 1, st_value := value }

private def undefSym (nameOff : UInt32) : Symbol.Symbol64 :=
  { (default : Symbol.Symbol64) with
    st_name := nameOff, st_info := (1 : UInt8) <<< 4
    st_shndx := Symbol.SHN_UNDEF }

/-- main's undef `printf`, libc's def `printf`. -/
private def resolveG : DepGraph :=
  let (mainStrtab, mOffs) := packStrings #["printf"]
  let (libcStrtab, lOffs) := packStrings #["printf"]
  synthDepGraph #[
    synthObj "main"
      (needed := #["libc.so"])
      (symtab := #[default, undefSym mOffs[0]!.toUInt32])
      (strtab := mainStrtab),
    synthObj "libc.so"
      (symtab := #[default, defSym lOffs[0]!.toUInt32 0xc0ffee])
      (strtab := libcStrtab) ]

#guard (resolveByName resolveG "printf").map (·.objectIdx) = some 1
#guard (resolveByName resolveG "nonexistent")              = none
#guard (buildTable    resolveG).missing.size               = 0

end UnitTest

end LeanLoad.Resolve

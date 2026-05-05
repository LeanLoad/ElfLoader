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
`Closure.objects` array (which `Discover` already returns in BFS
order: main first, then NEEDED entries in their declared order).
-/

import LeanLoad.Discover
import LeanLoad.Parse

namespace LeanLoad.Link.Resolve

open LeanLoad
open LeanLoad.Parse

/-- A resolved global symbol: its providing object's index in the
    `Closure.objects` array and the symbol's index within that
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
  Symbol.StringTable.lookup obj.elf.strtab sym.st_name.toNat

/-- Look up `name` as a global definition in `obj`'s symbol table. -/
def findInObject (obj : Discover.LoadedObject) (name : String) : Option Nat :=
  obj.elf.symtab.findIdx? fun sym =>
    isGlobalDef sym && symName obj sym == some name

/-- Resolve `name` against `li` via breadth-first search over its
    objects. Returns the providing `SymRef`, or `none` if no object
    defines it. -/
def resolveByName (li : Discover.Closure) (name : String) : Option SymRef := Id.run do
  let mut idx := 0
  for obj in li.objects do
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
    `Closure`. -/
structure ResolutionTable where
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
def buildTable (li : Discover.Closure) : ResolutionTable := Id.run do
  let mut resolved : Array (Unresolved × Option SymRef) := #[]
  let mut missing : Array Unresolved := #[]
  let mut weakMissing : Array Unresolved := #[]
  let mut objIdx := 0
  for obj in li.objects do
    let mut symIdx := 0
    for sym in obj.elf.symtab do
      if isUndef sym then
        match symName obj sym with
        | none    => pure ()
        | some "" => pure ()
        | some n =>
          let entry : Unresolved := { objectIdx := objIdx, symIdx, name := n }
          let r := resolveByName li n
          resolved := resolved.push (entry, r)
          if r.isNone then
            if isWeak sym then weakMissing := weakMissing.push entry
            else missing := missing.push entry
      symIdx := symIdx + 1
    objIdx := objIdx + 1
  return { resolved, missing, weakMissing }

end LeanLoad.Link.Resolve

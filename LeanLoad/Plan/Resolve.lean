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
`ObjectList.objects` array (which `Discover` already returns in BFS
order: main first, then NEEDED entries in their declared order).
-/

import LeanLoad.Plan.Discover
import LeanLoad.Parse.Structs
import LeanLoad.Elaborate.Elf
import LeanLoad.Fixtures

namespace LeanLoad.Resolve

open LeanLoad
open LeanLoad.Parse
open LeanLoad.Discover

/-- A resolved global symbol, parameterised by the dep graph's
    object count `n`. The `Fin n` carries the bounds proof at the
    type level — every consumer indexes `g.val` totally, no `?`. The
    `symIdx : Nat` stays unbounded because its valid range depends
    on the specific object referenced; consumers still `[]?` it. -/
structure SymRef (n : Nat) where
  objectIdx : Fin n
  symIdx    : Nat
  deriving Repr

/-- Look up `name` as a global definition in `obj`'s symbol table.
    Names are pre-resolved at validation time (see `Elaborate.Symbol`),
    so no string-table lookup happens here. The per-symbol `isGlobalDef`
    predicate lives on `Symbol64` directly (`Parse.Symbol`). -/
def findInObject (obj : Discover.LoadedObject) (name : String) :
    Option (Fin obj.elf.symtab.size) :=
  match h : obj.elf.symtab.findIdx? (fun entry =>
      entry.isGlobalDef && entry.name == some name) with
  | none   => none
  | some i => some ⟨i, (Array.findIdx?_eq_some_iff_findIdx_eq.mp h).1⟩

/-- Resolve `name` against `g` via breadth-first search over its
    objects. Returns the providing `SymRef`, or `none` if no object
    defines it. -/
def resolveByName (g : ObjectList) (name : String) : Option (SymRef g.val.size) := Id.run do
  for h : objectIdx in [:g.val.size] do
    if let some symIdx := findInObject g.val[objectIdx] name then
      return some { objectIdx := ⟨objectIdx, h.upper⟩, symIdx := symIdx.val }
  return none

/-- A failed-to-resolve undefined symbol; useful for diagnostics.
    Same `Fin n` parameterisation as `SymRef` so `Table.missing[i].objectIdx`
    is total. -/
structure Unresolved (n : Nat) where
  objectIdx : Fin n
  symIdx    : Nat
  name      : String
  deriving Repr

/-- Result of building the resolution table for an entire
    `ObjectList`. Parameterised by the dep graph's object count so
    every contained `Unresolved` / `SymRef` carries its bounds
    proof. -/
structure Table (n : Nat) where
  /-- One entry per undefined reference in any object. -/
  resolved : Array (Unresolved n × Option (SymRef n))
  /-- Strong (non-weak) undef references that did not resolve.
      A non-empty `missing` means the program would fail at load. -/
  missing  : Array (Unresolved n)
  /-- Weak undef references that did not resolve. Allowed by gabi 05;
      surfaced for diagnostics only. -/
  weakMissing : Array (Unresolved n)
  deriving Repr

/-- Walk every object's symbol table, look up each undefined
    reference's definition. -/
def buildTable (g : ObjectList) : Table g.val.size := Id.run do
  let mut resolved : Array (Unresolved g.val.size × Option (SymRef g.val.size)) := #[]
  let mut missing : Array (Unresolved g.val.size) := #[]
  let mut weakMissing : Array (Unresolved g.val.size) := #[]
  for h : objectIdx in [:g.val.size] do
    let obj := g.val[objectIdx]
    let mut symIdx := 0
    for symEntry in obj.elf.symtab do
      if symEntry.isUndef then
        match symEntry.name with
        | none    => pure ()
        | some "" => pure ()
        | some n =>
          let entry : Unresolved g.val.size :=
            { objectIdx := ⟨objectIdx, h.upper⟩, symIdx, name := n }
          let r := resolveByName g n
          resolved := resolved.push (entry, r)
          if r.isNone then
            if symEntry.isWeak then weakMissing := weakMissing.push entry
            else missing := missing.push entry
      symIdx := symIdx + 1
  return { resolved, missing, weakMissing }

-- ============================================================================
-- Compile-time unit tests: synthesise a tiny `ObjectList` where main has an
-- undefined ref to `printf` and libc defines it, then check the
-- resolver finds the right pair.
-- ============================================================================
section Example
open LeanLoad.Fixtures

private def defSym (name : String) (value : UInt64) : Elaborate.Symbol :=
  { name := some name, bind := .global, shndx := .concrete 1, value }

private def undefSym (name : String) : Elaborate.Symbol :=
  { name := some name, bind := .global, shndx := .undef, value := 0 }

/-- main's undef `printf`, libc's def `printf`. -/
private def resolveG : ObjectList :=
  ⟨#[
    synthObj "main"
      (needed := #["libc.so"])
      (symtab := #[default, undefSym "printf"]),
    synthObj "libc.so"
      (symtab := #[default, defSym "printf" 0xc0ffee]) ], by simp⟩

#guard (resolveByName resolveG "printf").map (·.objectIdx.val) = some 1
#guard (resolveByName resolveG "nonexistent")              = none
#guard (buildTable    resolveG).missing.size               = 0

end Example

end LeanLoad.Resolve

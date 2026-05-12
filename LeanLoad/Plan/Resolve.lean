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

Each entry's resolution is one of three explicit cases:
  • `found ref` — the BFS turned up a defining (object, symbol).
  • `weakUndef` — undef reference is weak (gabi 05 lets it bind to 0).
  • `strongUndef` — undef reference is strong and would fail at load.

`missing` and `weakMissing` are derived projections over `entries`,
not separately maintained arrays — the inductive `Resolution` is the
single source of truth.
-/

import LeanLoad.Parse.Structs
import LeanLoad.Elaborate.Elf
import Std.Data.HashMap

namespace LeanLoad.Resolve

open LeanLoad
open LeanLoad.Parse
open LeanLoad.Elaborate

/-- A resolved global symbol, parameterised by the elf-array size `n`.
    The `Fin n` carries the bounds proof at the type level — every
    consumer indexes the elf array totally, no `?`. The `symIdx : Nat`
    stays unbounded because its valid range depends on the specific
    object referenced; consumers still `[]?` it. -/
structure SymRef (n : Nat) where
  objectIdx : Fin n
  symIdx    : Nat
  deriving Repr

/-- Look up `name` as a global definition in `elf`'s symbol table.
    Names are pre-resolved at validation time (see `Elaborate.Symbol`),
    so no string-table lookup happens here. -/
def findInElf (elf : Elaborate.Elf) (name : String) : Option Nat :=
  elf.symtab.findIdx? (fun entry => entry.isGlobalDef && entry.name == some name)

/-- Resolve `name` against `elfs` via breadth-first search.
    Returns the providing `SymRef`, or `none` if no elf defines it. -/
def resolveByName (elfs : Array Elf) (name : String) : Option (SymRef elfs.size) := Id.run do
  for h : objectIdx in [:elfs.size] do
    if let some symIdx := findInElf elfs[objectIdx] name then
      return some { objectIdx := ⟨objectIdx, h.upper⟩, symIdx }
  return none

/-- A failed-to-resolve undefined symbol; useful for diagnostics.
    Same `Fin n` parameterisation as `SymRef` so `Table.missing[i].objectIdx`
    is total. -/
structure Unresolved (n : Nat) where
  objectIdx : Fin n
  symIdx    : Nat
  name      : String
  deriving Repr

/-- Result of resolving one undef reference. Three explicit cases:
    found, weak-undefined (S = 0 by spec), and strong-undefined (load
    failure). -/
inductive Resolution (n : Nat) where
  /-- The BFS found a providing `(object, symbol)`. -/
  | found (ref : SymRef n)
  /-- Undef reference is `STB_WEAK`; gabi 05 binds it to 0. -/
  | weakUndef
  /-- Undef reference is strong and unresolved — load failure. -/
  | strongUndef
  deriving Repr

namespace Resolution

/-- Extract the resolved provider, dropping the weak/strong-undef
    distinction. Used by `Reloc.planOne` where both undef branches
    collapse to `S = 0`. -/
def target? : Resolution n → Option (SymRef n)
  | .found ref => some ref
  | .weakUndef => none
  | .strongUndef => none

end Resolution

/-- Result of building the resolution table for the elf array.
    Parameterised by the elf count so every contained `Unresolved` /
    `SymRef` carries its bounds proof. -/
structure Table (n : Nat) where
  /-- One entry per undefined reference in any elf, in iteration
      order. Each carries an explicit `Resolution` — there's no
      `Option` to distinguish "weak undef" from "strong undef". -/
  entries : Array (Unresolved n × Resolution n)
  /-- O(1) `(objectIdx, symIdx) → Resolution n` lookup, in lock-step
      with `entries`. `Plan.Reloc.planOne` reads this so per-rela
      symbol resolution is O(1). -/
  index : Std.HashMap (Nat × Nat) (Resolution n)

namespace Table

/-- Strong (non-weak) undef references that did not resolve. A
    non-empty `missing` means the program would fail at load. -/
def missing (t : Table n) : Array (Unresolved n) :=
  t.entries.filterMap fun (u, r) => match r with
    | .strongUndef => some u
    | _            => none

/-- Weak undef references that did not resolve. Allowed by gabi 05;
    surfaced for diagnostics only. -/
def weakMissing (t : Table n) : Array (Unresolved n) :=
  t.entries.filterMap fun (u, r) => match r with
    | .weakUndef => some u
    | _          => none

end Table

/-- Walk every elf's symbol table, look up each undefined
    reference's definition. Builds both the iteration array
    (`entries`) and the O(1) lookup `index` in lock-step. -/
def buildTable (elfs : Array Elf) : Table elfs.size := Id.run do
  let mut entries : Array (Unresolved elfs.size × Resolution elfs.size) := #[]
  let mut index : Std.HashMap (Nat × Nat) (Resolution elfs.size) := ∅
  for h : objectIdx in [:elfs.size] do
    let elf := elfs[objectIdx]
    let mut symIdx := 0
    for symEntry in elf.symtab do
      if symEntry.isUndef then
        match symEntry.name with
        | none    => pure ()
        | some "" => pure ()
        | some n =>
          let entry : Unresolved elfs.size :=
            { objectIdx := ⟨objectIdx, h.upper⟩, symIdx, name := n }
          let resolution : Resolution elfs.size :=
            match resolveByName elfs n with
            | some ref => .found ref
            | none     => if symEntry.isWeak then .weakUndef else .strongUndef
          entries := entries.push (entry, resolution)
          index := index.insert (objectIdx, symIdx) resolution
      symIdx := symIdx + 1
  return { entries, index }

end LeanLoad.Resolve

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

/-- Result of building the resolution table for the elf array.
    Parameterised by the elf count so every contained `Unresolved` /
    `SymRef` carries its bounds proof. -/
structure Table (n : Nat) where
  /-- One entry per undefined reference in any elf. Iteration order —
      used by the debug printer in `Main.debug`. -/
  resolved : Array (Unresolved n × Option (SymRef n))
  /-- O(1) `(objectIdx, symIdx) → Option (SymRef n)` lookup. Built
      in lock-step with `resolved`; `Plan.Reloc.lookupResolved` reads
      this so per-rela symbol resolution is O(1) instead of scanning
      `resolved` linearly (which was O(undefs × relas) in aggregate). -/
  index : Std.HashMap (Nat × Nat) (Option (SymRef n))
  /-- Strong (non-weak) undef references that did not resolve.
      A non-empty `missing` means the program would fail at load. -/
  missing  : Array (Unresolved n)
  /-- Weak undef references that did not resolve. Allowed by gabi 05;
      surfaced for diagnostics only. -/
  weakMissing : Array (Unresolved n)

/-- Walk every elf's symbol table, look up each undefined
    reference's definition. Builds both the iteration array
    (`resolved`) and the O(1) lookup `index` in lock-step. -/
def buildTable (elfs : Array Elf) : Table elfs.size := Id.run do
  let mut resolved : Array (Unresolved elfs.size × Option (SymRef elfs.size)) := #[]
  let mut index : Std.HashMap (Nat × Nat) (Option (SymRef elfs.size)) := ∅
  let mut missing : Array (Unresolved elfs.size) := #[]
  let mut weakMissing : Array (Unresolved elfs.size) := #[]
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
          let r := resolveByName elfs n
          resolved := resolved.push (entry, r)
          index := index.insert (objectIdx, symIdx) r
          if r.isNone then
            if symEntry.isWeak then weakMissing := weakMissing.push entry
            else missing := missing.push entry
      symIdx := symIdx + 1
  return { resolved, index, missing, weakMissing }

end LeanLoad.Resolve

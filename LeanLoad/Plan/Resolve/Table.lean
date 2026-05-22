/-
Per-graph resolution table.

For each undef reference in every elf's symtab, run `resolveByName`
against `bfsOrder g` and record the outcome:

  • `STB_GLOBAL` undef → `.found ref` or `.strongUndef` (load failure).
  • `STB_WEAK` undef   → `.found ref` or `.weakUndef` (gabi 05: S = 0).
  • NoName / empty-name undef → `.weakUndef`. A strong-undef without
    a name is a malformed ELF; we tolerate it as weak rather than
    error, matching glibc/musl behaviour.

The result is a `Table objCount` carrying two parallel views:

  · `entries` — array of `(Unresolved, Resolution)` pairs for the
                *named* undefs only. Used for diagnostics.
  · `index`   — `(objectIdx, symIdx) → Resolution` HashMap covering
                *every* undef. `Table.lookup` is total — `Reloc.planOne`
                always gets a defined Resolution.

`Plan.Aggregate.ofGraph` calls `buildTable g` once and rejects any
graph whose `Table.missing` is non-empty.
-/

import LeanLoad.Plan.Resolve.Bfs
import LeanLoad.Plan.Resolve.Lookup
import Std.Data.HashMap

namespace LeanLoad.Plan.Resolve

open LeanLoad
open LeanLoad.Elaborate (Elf)
open LeanLoad.Discover (LoadGraph)

/-- Result of resolving one undef reference. Three explicit cases:
    found, weak-undefined (S = 0 by spec), and strong-undefined (load
    failure). -/
inductive Resolution (objCount : Nat) where
  /-- The BFS found a providing `(object, symbol)`. -/
  | found (ref : SymRef objCount)
  /-- Undef reference is `STB_WEAK`; gabi 05 binds it to 0. -/
  | weakUndef
  /-- Undef reference is strong and unresolved — load failure. -/
  | strongUndef
  deriving Repr

namespace Resolution

/-- Extract the resolved provider, dropping the weak/strong-undef
    distinction. Used by `Reloc.planOne` where both undef branches
    collapse to `S = 0`. -/
def target? : Resolution objCount → Option (SymRef objCount)
  | .found ref => some ref
  | .weakUndef => none
  | .strongUndef => none

end Resolution

/-- Result of building the resolution table for the elf array.
    Parameterised by the elf count so every contained `Unresolved` /
    `SymRef` carries its bounds proof.

    `index` is *total over all undefined symbols* (not just those with
    a name): `buildTable` inserts `weakUndef` for noName / empty-name
    undefs, so any per-rela lookup `lookup objectIdx symIdx` always
    returns a defined `Resolution`. `entries` is the diagnostic /
    iteration array and skips noName entries (they have no useful
    diagnostic name to surface). -/
structure Table (objCount : Nat) where
  /-- One entry per *named* undefined reference, in iteration order.
      Used for diagnostics (`missing` / `weakMissing` projections);
      noName / empty-name undefs are not included. -/
  entries : Array (Unresolved objCount × Resolution objCount)
  /-- O(1) `(objectIdx, symIdx) → Resolution objCount` lookup, total over all
      undefined symbols (named or not). Consumers go through
      `Table.lookup` so the type's totality guarantee shows up at the
      call site. -/
  index : Std.HashMap (Nat × Nat) (Resolution objCount)

namespace Table

/-- Total `(objectIdx, symIdx) → Resolution` lookup. Falls back to
    `weakUndef` when the key is missing — but for tables built by
    `buildTable` over an elf's `isUndef` symbols, the key is always
    present, so the fallback never fires. The `getD` form lets
    `Plan.Reloc.resolveTarget` pattern-match three constructors
    (`.found` / `.weakUndef` / `.strongUndef`) instead of four (those
    + `none`). -/
def lookup (t : Table objCount) (objectIdx symIdx : Nat) : Resolution objCount :=
  t.index.getD (objectIdx, symIdx) .weakUndef

/-- Strong (non-weak) undef references that did not resolve. A
    non-empty `missing` means the program would fail at load. -/
def missing (t : Table objCount) : Array (Unresolved objCount) :=
  t.entries.filterMap fun (u, r) => match r with
    | .strongUndef => some u
    | _            => none

/-- Weak undef references that did not resolve. Allowed by gabi 05;
    surfaced for diagnostics only. -/
def weakMissing (t : Table objCount) : Array (Unresolved objCount) :=
  t.entries.filterMap fun (u, r) => match r with
    | .weakUndef => some u
    | _          => none

end Table

/-- Walk every elf's symbol table, look up each undefined
    reference's definition along the BFS order. Builds both the
    diagnostic iteration array (`entries`) and the O(1) total lookup
    `index`.

    `index` covers *every* undefined symbol — named or not — so
    `Table.lookup` is total. NoName / empty-name undefs map to
    `weakUndef` (gabi 05's safe fallback for an unresolvable weak
    reference; a strong-undef without a name is a malformed ELF that
    the linker shouldn't have produced). `entries` skips them since
    they have no useful diagnostic string.

    The BFS order over `(g.objects, g.deps)` is computed once via
    `bfsOrder g` and reused across every undef lookup. -/
def buildTable (g : LoadGraph) : Table g.objects.size := Id.run do
  let order := bfsOrder g
  let mut entries : Array (Unresolved g.objects.size × Resolution g.objects.size) := #[]
  let mut index : Std.HashMap (Nat × Nat) (Resolution g.objects.size) := ∅
  for h : objectIdx in [:g.objects.size] do
    let elf := g.objects[objectIdx].elf
    let mut symIdx := 0
    for symEntry in elf.symtab do
      if symEntry.isUndef then
        match symEntry.name with
        | none =>
          index := index.insert (objectIdx, symIdx) .weakUndef
        | some "" =>
          index := index.insert (objectIdx, symIdx) .weakUndef
        | some symName =>
          let entry : Unresolved g.objects.size :=
            { objectIdx := ⟨objectIdx, h.upper⟩, symIdx, name := symName }
          let resolution : Resolution g.objects.size :=
            match resolveByName g order symName with
            | some ref => .found ref
            | none     => if symEntry.isWeak then .weakUndef else .strongUndef
          entries := entries.push (entry, resolution)
          index := index.insert (objectIdx, symIdx) resolution
      symIdx := symIdx + 1
  return { entries, index }

end LeanLoad.Plan.Resolve

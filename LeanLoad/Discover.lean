/-
Discover stage public interface.

Discover turns a main executable path into a witnessed dependency graph:

  · `LoadedObject` — one checked ELF plus its canonical discovery name.
  · `LoadGraph` — every transitively-needed object, dependency edges, and
    init order, with invariants that make downstream access total.
  · `WorkItem` — the explicit pending dependency request consumed by the
    traversal implementation.
  · `ResolvedObject` / `DependencyFinder` — the path-search/open/parse seam used by
    production IO and by pure examples.

Implementation details live below `LeanLoad/Discover/`: `State`
maintains the construction state, `DFS` resolves work items, `Build`
promotes the final discovered set to `LoadGraph`, and `IO` wires the production
finder.
-/

import LeanLoad.Parse
import LeanLoad.Runtime

namespace LeanLoad.Discover

open LeanLoad
open LeanLoad.Parse

-- ============================================================================
-- LoadedObject — one entry of the graph.
-- ============================================================================

/-- One loaded object. Production policy (`Discover/Runtime.lean`):
    NEEDED-loaded deps must have `DT_SONAME` (used as `.name`);
    the main executable's `.name` is `basename mainPath` (executables
    conventionally don't set SONAME). -/
structure LoadedObject where
  /-- Canonical dedup key. For NEEDED deps: `elf.soname.get!` (production
      requires DT_SONAME). For the main executable: `basename mainPath`. -/
  name : String
  /-- Open read-only file, kept for `pread` (parsing extras) and
      `mmap` (Exec stage). Production paths always carry a real
      fd plus observed size; examples use a dummy `Runtime.File`. -/
  handle : Runtime.File
  /-- Checked ELF — output of `Parse.parse`. The type is the witness
      that PT_LOAD well-formedness held and every dynamic relocation
      was located against a covering segment. -/
  elf  : Elf
  deriving Repr

namespace LoadedObject

/-- Construct the main `LoadedObject` from a user-supplied path. The
    canonical name is the path basename — executables don't conventionally
    set DT_SONAME, and main is path-loaded (not NEEDED-driven), so we
    don't consult `elf.soname`. -/
def ofMain (mainPath : String) (handle : Runtime.File)
    (elf : Elf) : LoadedObject :=
  { name := (mainPath.splitOn "/").getLast?.getD mainPath, handle, elf }

end LoadedObject

-- ============================================================================
-- LoadGraph — the bundled output of Discover.
-- ============================================================================

/-- Output of `Discover` — every transitively-NEEDED object loaded,
    indexed for `Fin`-total downstream access, with the dep graph and
    a DFS post-order init sequence bundled. The specific *traversal*
    order Discover used is an implementation detail: only `[0] = main`
    is spec-relevant. Symbol resolution (gabi 08 § Shared Object
    Dependencies) iterates BFS-from-0 over `deps` — see
    `Reloc.Symbol.bfsOrder` — and doesn't depend on `objects`'s
    intrinsic order. -/
structure LoadGraph where
  /-- The loaded objects, indexed in an implementation-defined order
      whose only spec-relevant property is `objects[0] = main` (the
      `Discover` seed). Consumers that need a particular traversal
      order compute it explicitly from `deps` — e.g. BFS for symbol
      resolution (`Reloc.Symbol.bfsOrder`), DFS post-order for init
      (already bundled as `initOrder`). -/
  objects     : Array LoadedObject
  /-- Per-object dependency indices, recorded during discovery. Parallel to
      `objects` and complete: every NEEDED has been resolved to an
      idx in `deps[i]`. -/
  deps        : Array (Array Nat)
  /-- DFS post-order over the dep graph: indices in the order each
      object's `discoverWork` returned. Used as the init order (deps before
      dependents, cycles undefined per gabi 08). Established during
      `discoverWith` via `State.markComplete`. -/
  initOrder   : Array (Fin objects.size)
  /-- Non-emptiness — witnessed by `State.initial` seeding with main
      before discovery begins. -/
  sizePos     : 0 < objects.size
  /-- Names pairwise distinct. Witnessed by the `nameIx` dedup check before
      each push. -/
  namesNodup  : (objects.map (·.name)).toList.Nodup
  /-- `deps` is parallel to `objects`. -/
  depsSize    : deps.size = objects.size
  /-- Every recorded edge target is a valid index into `objects`. -/
  depsBounds  : ∀ (i : Nat) (h : i < deps.size), ∀ t ∈ deps[i], t < objects.size
  /-- Closure under NEEDED: every object's `deps` row holds exactly one
      entry per `DT_NEEDED` of its elf. Established at the end of
      `discoverWith` once the top-level traversal has returned. -/
  closure     : ∀ (i : Nat) (h : i < objects.size),
    (deps[i]'(by rw [depsSize]; exact h)).size = (objects[i]'h).elf.needed.size
  /-- `initOrder` is parallel to `objects` — every object appears
      exactly once. -/
  initOrderSize  : initOrder.size = objects.size
  /-- No duplicate indices in `initOrder` (treated as `Nat` via `.val`).
      Combined with `initOrderSize`, makes `initOrder` a permutation
      of `[0, objects.size)`. -/
  initOrderNodup : (initOrder.toList.map (·.val)).Nodup
  deriving Repr

namespace LoadGraph

/-- The main executable — total because `LoadGraph` carries `sizePos`. -/
def main (g : LoadGraph) : LoadedObject := g.objects[0]'g.sizePos

/-- Single-step dependency edge in the loaded graph: `j ∈ deps[i]`.
    Defined on `Nat × Nat`; the `i < g.deps.size` hypothesis is part
    of the existential so the relation can be lifted through
    `Reachable` without a Fin wrapper. -/
def Step (g : LoadGraph) (i j : Nat) : Prop :=
  ∃ (h : i < g.deps.size), j ∈ g.deps[i]'h

/-- Reachable from `i` to `j` via dep edges (reflexive-transitive
    closure of `Step`). Spec witness for the gabi 08 § Shared Object
    Dependencies "dependency graph" — every NEEDED chain from main is
    a path under this relation. -/
inductive Reachable (g : LoadGraph) : Nat → Nat → Prop
  /-- Every node is reachable from itself in zero steps. -/
  | refl (i : Nat) : Reachable g i i
  /-- Extending a reachability path by one edge. -/
  | tail {i j k : Nat} (h_ij : Reachable g i j) (h_jk : g.Step j k) :
      Reachable g i k

/-- Reachable from main (idx 0). Convenience for the most common case. -/
def ReachableFromMain (g : LoadGraph) (i : Nat) : Prop :=
  g.Reachable 0 i

end LoadGraph

-- ============================================================================
-- WorkItem / DependencyFinder — the dependency-resolution boundary.
-- ============================================================================

/-- One dependency request to resolve next. `needed` is the raw `DT_NEEDED`
    string from the referring object; `runpath` is that object's
    `DT_RUNPATH`, if present. This keeps traversal work explicit instead
    of passing loose strings around. -/
structure WorkItem where
  needed  : String
  runpath : Option String
  deriving Repr

namespace WorkItem

/-- Build the work items created by one object's `DT_NEEDED` array. -/
def ofNeededArray (runpath : Option String) (needed : Array String) :
    List WorkItem :=
  needed.toList.map (fun name => { needed := name, runpath })

end WorkItem

/-- A resolved dependency, ready to insert into the discovered set. `name`
    is the canonical dedup key (`DT_SONAME` in production). -/
structure ResolvedObject where
  name   : String
  handle : Runtime.File
  elf    : LeanLoad.Parse.Elf
  deriving Repr

/-- Dependency finder seam used by discovery traversal.

    Production `DependencyFinder.io` performs runtime path search, open, and checked
    parse. Examples use an in-memory finder. -/
structure DependencyFinder (m : Type → Type) where
  /-- Find a dependency for this work item. `none` means "not found"; parse failures and
      policy failures escape through the monad's error mechanism. -/
  find : WorkItem → m (Option ResolvedObject)
  /-- Surface a fatal error. Polymorphic because callers use it in
      continuation position. -/
  fail    : {α : Type} → String → m α

end LeanLoad.Discover

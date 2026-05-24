/-
Discover stage public interface.

Discover's core turns a main object plus a monadic dependency finder into a
witnessed dependency graph:

  · `LoadedObject` — one checked ELF plus its canonical discovery name.
  · `LoadGraph` — every transitively-needed object, dependency edges, and
    init order, with invariants that make downstream access total.
  · `WorkItem` — the explicit pending dependency request consumed by the
    traversal implementation.
  · `ObjectFinder` — the path-search/open/parse seam used by
    the CLI and by pure examples.

Implementation details live below `LeanLoad/Discover/`: `Discovered`
maintains the construction state, `Traversal` resolves work items, and
`Finalize` promotes the final discovered set to `LoadGraph`.
-/

import LeanLoad.Parse
import LeanLoad.Runtime.Basic

namespace LeanLoad.Discover

open LeanLoad
open LeanLoad.Parse

-- ============================================================================
-- LoadedObject — one entry of the graph.
-- ============================================================================

/-- One loaded object. Production policy:
    NEEDED-loaded deps must have `DT_SONAME` (used as `.name`);
    the main executable's `.name` is `basename mainPath` (executables
    conventionally don't set SONAME). -/
structure LoadedObject where
  /-- Canonical dedup key. For NEEDED deps: `elf.soname.get!` (production
      requires DT_SONAME). For the main executable: `basename mainPath`. -/
  name : String
  /-- Open read-only file, kept for `pread` (parsing extras) and
      `mmap` (Finalize stage). Production paths always carry a real
      fd plus observed size; examples use a dummy `Runtime.File`. -/
  handle : Runtime.File
  /-- Checked ELF — output of `Parse.parseM`. The type is the witness
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
-- Init-order predicates.
-- ============================================================================

namespace LoadGraph

/-- `a` appears before `b` in an array of natural indices. This is the raw
    postorder relation used before `LoadGraph.initOrder` wraps indices as
    `Fin`s. -/
def PostBefore (order : Array Nat) (a b : Nat) : Prop :=
  ∃ ia ib : Nat,
    order[ia]? = some a ∧
    order[ib]? = some b ∧
    ia < ib

/-- If `a` is already present, then appending `b` places `a` before `b`. -/
theorem PostBefore.push_right {order : Array Nat} {a b : Nat}
    (ha : a ∈ order.toList) : PostBefore (order.push b) a b := by
  have ha_arr : a ∈ order := Array.mem_toList_iff.mp ha
  obtain ⟨ia, hia⟩ := Array.mem_iff_getElem?.mp ha_arr
  have hia_lt : ia < order.size := by
    obtain ⟨h, _⟩ := Array.getElem?_eq_some_iff.mp hia
    exact h
  refine ⟨ia, order.size, ?_, ?_, hia_lt⟩
  · rw [Array.getElem?_push]
    have h_ne : ia ≠ order.size := Nat.ne_of_lt hia_lt
    rw [if_neg h_ne]
    exact hia
  · rw [Array.getElem?_push, if_pos rfl]

/-- Appending one more index preserves an existing before relation. -/
theorem PostBefore.push_preserved {order : Array Nat} {a b c : Nat}
    (h : PostBefore order a b) : PostBefore (order.push c) a b := by
  rcases h with ⟨ia, ib, hia, hib, hlt⟩
  have hia_lt : ia < order.size := (Array.getElem?_eq_some_iff.mp hia).1
  have hib_lt : ib < order.size := (Array.getElem?_eq_some_iff.mp hib).1
  refine ⟨ia, ib, ?_, ?_, hlt⟩
  · rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hia_lt)]
    exact hia
  · rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hib_lt)]
    exact hib

end LoadGraph

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
      dependents). Discover rejects cyclic dependencies because gabi 08 leaves
      cyclic init ordering undefined. Established during `discoverFrom` via
      `Discovered.markComplete`. -/
  initOrder   : Array (Fin objects.size)
  /-- Non-emptiness — witnessed by `Discovered.initial` seeding with main
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
      `discoverFrom` once the top-level traversal has returned. -/
  closure     : ∀ (i : Nat) (h : i < objects.size),
    (deps[i]'(by rw [depsSize]; exact h)).size = (objects[i]'h).elf.needed.size
  /-- `initOrder` is parallel to `objects`. -/
  initOrderSize  : initOrder.size = objects.size
  /-- Every object index appears in `initOrder`. Together with `Fin`-typed
      entries and `initOrderNodup`, this is the direct permutation witness
      downstream proofs should consume. -/
  initOrderCovers : ∀ i, i < objects.size →
    i ∈ (initOrder.map (fun ix => ix.val)).toList
  /-- No duplicate indices in `initOrder` (treated as `Nat` via `.val`).
      Combined with `initOrderCovers`, makes `initOrder` a permutation
      of `[0, objects.size)`. -/
  initOrderNodup : (initOrder.toList.map (·.val)).Nodup
  /-- DFS init order is dependency-before-dependent for every recorded
      `DT_NEEDED` edge. Discover rejects active-stack cycles while building the
      graph; gabi 08 leaves cyclic init order undefined, so produced graphs
      carry the stronger acyclic edge-order property. -/
  initOrderRespectsDeps :
    ∀ i j, (∃ h : i < deps.size, j ∈ deps[i]'h) →
      LoadGraph.PostBefore (initOrder.map (fun ix => ix.val)) j i
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

/-- `a` appears before `b` in `g.initOrder`.

    The arguments are `Fin g.objects.size`, so the index-in-bounds part of the
    init-order invariant is carried by the type. -/
def InitBefore (g : LoadGraph) (a b : Fin g.objects.size) : Prop :=
  ∃ ia ib : Nat,
    g.initOrder[ia]? = some a ∧
    g.initOrder[ib]? = some b ∧
    ia < ib

/-- Nat-index wrapper around `InitBefore`, useful when working from `g.Step`
    edges, whose endpoints are Nat-valued. Bounds are carried by the `Fin`
    entries inside `initOrder`; this wrapper intentionally compares their
    underlying natural indices. -/
def InitBeforeIdx (g : LoadGraph) (a b : Nat) : Prop :=
  PostBefore (g.initOrder.map (fun ix => ix.val)) a b

/-- Every object index appears in `g.initOrder`. Bounds are carried by the `Fin`
    entries; this predicate names the coverage half of the init-order
    permutation witness. -/
def InitOrderCovers (g : LoadGraph) : Prop :=
  ∀ i, i < g.objects.size → i ∈ (g.initOrder.map (fun ix => ix.val)).toList

/-- Init-order topological property for produced graphs.

    For a direct dependency edge `i → j`, the dependency `j` appears before its
    dependent `i`. Discover rejects active-stack cycles while building the graph;
    gabi 08 leaves cyclic init ordering undefined. -/
def InitOrderRespectsDeps (g : LoadGraph) : Prop :=
  ∀ i j, g.Step i j → g.InitBeforeIdx j i

theorem initOrderCovers_spec (g : LoadGraph) :
    g.InitOrderCovers :=
  g.initOrderCovers

theorem initOrderRespectsDeps_spec (g : LoadGraph) :
    g.InitOrderRespectsDeps := by
  intro i j h_step
  exact g.initOrderRespectsDeps i j h_step

end LoadGraph

-- ============================================================================
-- WorkItem / ObjectFinder — the object-discovery boundary.
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

/-- Object finder seam used by discovery traversal.

    The production object finder performs runtime path search, open, and checked
    parse. Examples use an in-memory finder. -/
structure ObjectFinder (m : Type → Type) where
  /-- Find and parse the main object. This owns the effectful boundary from a user
      path to the checked `LoadedObject` that seeds traversal. -/
  findMain : String → m LoadedObject
  /-- Find a dependency for this work item. `none` means "not found"; parse failures and
      policy failures escape through the monad's error mechanism. -/
  findDependency : WorkItem → m (Option LoadedObject)

end LeanLoad.Discover

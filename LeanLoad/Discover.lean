/-
Discover stage public core types.

Discover turns a path-loaded main object plus a monadic dependency provider
into a witnessed dependency graph plus derived init order. This root module is
the foundation imported by the stage submodules:

  · `Names` / `Provider` — naming policy and effect boundary.
  · `Graph` — graph reachability theorems.
  · `Order` — raw order lemmas and init-order proofs.
  · `Builder` / `Traversal` / `Finalize` — construction state, DFS, and
    final promotion.
-/

import LeanLoad.Parse
import LeanLoad.Runtime

namespace LeanLoad.Discover

open LeanLoad
open LeanLoad.Parse

/-- One discovered object. Production policy:
    NEEDED deps must have `DT_SONAME` (used as `.name`);
    the main executable's `.name` is `basename mainPath` (executables
    conventionally don't set SONAME). -/
structure DiscoveredObject where
  /-- Canonical dedup key. For NEEDED deps: `elf.soname.get!` (production
      requires DT_SONAME). For the main executable: `basename mainPath`. -/
  name : String
  /-- Open read-only file, kept for extra parse reads and file-backed mmap.
      Production paths carry C-backed read/mmap closures plus observed size;
      examples use a dummy `Runtime.File`. -/
  handle : Runtime.File
  /-- Canonical directory used to expand this object's `$ORIGIN` dynamic strings
      (gABI 08 § Substitution Sequences), if the provider can supply one. -/
  originDir : Option String
  /-- Checked ELF — output of `Parse.parseFile`. The type is the witness
      that PT_LOAD well-formedness held and every dynamic relocation
      was located against a covering segment. -/
  elf : Elf
  deriving Repr

/-- One dependency request to resolve next. `needed` is the raw `DT_NEEDED`
    string from the referring object; `rpath`/`runpath` are that object's
    dynamic search paths, if present; `originDir` is the referring file's
    canonical directory for `$ORIGIN` expansion. This keeps the gABI 08 § Shared
    Object Dependencies search context explicit instead of passing loose strings
    around. -/
structure WorkItem where
  needed  : String
  originDir : Option String
  rpath   : Option String
  runpath : Option String
  deriving Repr

namespace WorkItem

/-- Build the work items created by one object's `DT_NEEDED` array. -/
def ofNeededArray (originDir rpath runpath : Option String) (needed : Array String) :
    List WorkItem :=
  needed.toList.map (fun name => { needed := name, originDir, rpath, runpath })

end WorkItem

/-- Dependency graph: every transitively-NEEDED object discovered, indexed for
    `Fin`-total downstream access, with complete `DT_NEEDED` edges. The
    specific *traversal* order Discover used is an implementation detail: only
    `[0] = main` is spec-relevant. Consumers derive schedules from `deps`, e.g.
    BFS for symbol resolution (`Reloc.Symbol.bfsOrder`) and DFS post-order for
    init/fini (`InitOrder`). -/
structure LoadGraph where
  /-- The discovered objects, indexed in an implementation-defined order
      whose only spec-relevant property is `objects[0] = main` (the
      `Discover` seed). Consumers that need a particular traversal
      order compute it explicitly from `deps` — e.g. BFS for symbol resolution
      (`Reloc.Symbol.bfsOrder`) and DFS post-order for init (`InitOrder`). -/
  objects     : Array DiscoveredObject
  /-- Per-object dependency indices, recorded during discovery. Parallel to
      `objects` and complete: every NEEDED has been resolved to an
      idx in `deps[i]`. -/
  deps        : Array (Array Nat)
  /-- Non-emptiness — witnessed by `Discovered.initial` seeding with main
      before discovery begins. -/
  sizePos     : 0 < objects.size
  /-- Names pairwise distinct. Witnessed by the discovery dedup check before
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
  deriving Repr

namespace LoadGraph

/-- The main executable — total because `LoadGraph` carries `sizePos`. -/
def main (g : LoadGraph) : DiscoveredObject := g.objects[0]'g.sizePos

/-- Single-step dependency edge in the discovered graph: `j ∈ deps[i]`.
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

/-- Nonempty reachability via dependency edges. Unlike `Reachable`, this has no
    zero-step reflexive constructor, so `DepPath g i i` is an actual dependency
    cycle. -/
inductive DepPath (g : LoadGraph) : Nat → Nat → Prop
  | step {i j : Nat} (h : g.Step i j) : DepPath g i j
  | tail {i j k : Nat} (h_ij : DepPath g i j) (h_jk : g.Step j k) :
      DepPath g i k

/-- No nonempty dependency path returns to its start. This names the usual DAG
    property for clients that want to reason about cycle-free graphs; Discover
    itself records cyclic graphs because gabi 08 § Shared Object Dependencies
    leaves cyclic initializer ordering unspecified rather than forbidden. -/
def Acyclic (g : LoadGraph) : Prop :=
  ∀ i, ¬ g.DepPath i i

/-- `a` appears before `b` in an array of natural indices. This is the raw
    postorder relation used before `InitOrder.order` wraps indices as `Fin`s. -/
def PostBefore (order : Array Nat) (a b : Nat) : Prop :=
  ∃ ia ib : Nat,
    order[ia]? = some a ∧
    order[ib]? = some b ∧
    ia < ib

end LoadGraph

/-- A graph-indexed init schedule. This is derived from `LoadGraph.deps`, not
    part of graph identity: the graph gives the dependency relation, while
    `InitOrder` certifies the deterministic DFS post-order chosen for
    initialization.

    For acyclic graphs this is the usual dependency-before-dependent order. For
    cyclic graphs, a dependency-before-dependent order cannot exist; the
    `classifiesDeps` field records that every edge is still placed in the total
    order, with reverse/self cases representing LeanLoad's deterministic cycle
    breaks. gabi 08 leaves cyclic init ordering undefined. -/
structure InitOrder (g : LoadGraph) where
  /-- Object indices in dependency-before-dependent init order. -/
  order : Array (Fin g.objects.size)
  /-- `order` is parallel to `g.objects`. -/
  size : order.size = g.objects.size
  /-- Every object index appears in `order`. Together with `Fin`-typed entries
      and `nodup`, this is the direct permutation witness downstream proofs
      should consume. -/
  covers : ∀ i, i < g.objects.size → i ∈ (order.map (fun ix => ix.val)).toList
  /-- No duplicate indices in `order` (treated as `Nat` via `.val`). -/
  nodup : (order.toList.map (·.val)).Nodup
  /-- Every recorded `DT_NEEDED` edge is placed in the total schedule. For an
      edge `i → j`, the `j = i` and `i`-before-`j` cases are deterministic
      cycle breaks; gabi 08 does not specify an order inside a dependency cycle. -/
  classifiesDeps :
    ∀ i j, g.Step i j →
      j = i ∨
      LoadGraph.PostBefore (order.map (fun ix => ix.val)) j i ∨
      LoadGraph.PostBefore (order.map (fun ix => ix.val)) i j
  deriving Repr

/-- Public Discover result: the dependency graph plus the init schedule derived
    from that graph. Keeping the schedule here (rather than inside `LoadGraph`)
    makes graph identity just objects + dependency edges. -/
structure Result where
  graph : LoadGraph
  initOrder : InitOrder graph
  deriving Repr

end LeanLoad.Discover

/-
Final dependency graph produced by Discover.

`LoadGraph` is the public dependency relation: all transitively-needed objects
and their resolved dependency edges. Init/fini scheduling is a graph-indexed
`InitOrder`, not a field of the graph itself.
-/

import LeanLoad.Discover.Order

namespace LeanLoad.Discover

open LeanLoad

/-- Dependency graph: every transitively-NEEDED object loaded, indexed for
    `Fin`-total downstream access, with complete `DT_NEEDED` edges. The
    specific *traversal* order Discover used is an implementation detail: only
    `[0] = main` is spec-relevant. Consumers derive schedules from `deps`, e.g.
    BFS for symbol resolution (`Reloc.Symbol.bfsOrder`) and DFS post-order for
    init/fini (`InitOrder`). -/
structure LoadGraph where
  /-- The loaded objects, indexed in an implementation-defined order
      whose only spec-relevant property is `objects[0] = main` (the
      `Discover` seed). Consumers that need a particular traversal
      order compute it explicitly from `deps` — e.g. BFS for symbol resolution
      (`Reloc.Symbol.bfsOrder`) and DFS post-order for init (`InitOrder`). -/
  objects     : Array LoadedObject
  /-- Per-object dependency indices, recorded during discovery. Parallel to
      `objects` and complete: every NEEDED has been resolved to an
      idx in `deps[i]`. -/
  deps        : Array (Array Nat)
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

/-- A dependency edge's source is a valid object index. -/
theorem Step.src_lt_objects (g : LoadGraph) {i j : Nat} (h : g.Step i j) :
    i < g.objects.size := by
  rcases h with ⟨h_i, _h_j⟩
  rw [← g.depsSize]
  exact h_i

/-- A dependency edge's target is a valid object index. -/
theorem Step.tgt_lt_objects (g : LoadGraph) {i j : Nat} (h : g.Step i j) :
    j < g.objects.size := by
  rcases h with ⟨h_i, h_j⟩
  exact g.depsBounds i h_i j h_j

/-- Reachability from a valid source stays inside the graph. -/
theorem Reachable.tgt_lt_objects (g : LoadGraph) {i j : Nat}
    (h_i : i < g.objects.size) (h : g.Reachable i j) :
    j < g.objects.size := by
  induction h with
  | refl => exact h_i
  | tail _h_ij h_jk _ih => exact Step.tgt_lt_objects g h_jk

/-- Anything reachable from main is a valid object index. -/
theorem ReachableFromMain.lt_objects (g : LoadGraph) {i : Nat}
    (h : g.ReachableFromMain i) : i < g.objects.size := by
  unfold ReachableFromMain at h
  exact Reachable.tgt_lt_objects g g.sizePos h

end LoadGraph

/-- A graph-indexed init schedule. This is derived from `LoadGraph.deps`, not
    part of graph identity: the graph gives the dependency relation, while
    `InitOrder` certifies one dependency-before-dependent topological order.

    Discover computes this as DFS post-order and rejects cycles because gabi 08
    leaves cyclic init ordering undefined. -/
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
  /-- Every recorded `DT_NEEDED` edge is dependency-before-dependent in `order`. -/
  respectsDeps :
    ∀ i j, g.Step i j → LoadGraph.PostBefore (order.map (fun ix => ix.val)) j i
  deriving Repr

namespace InitOrder

/-- `a` appears before `b` in this init order.

    The arguments are `Fin g.objects.size`, so the index-in-bounds part of the
    init-order invariant is carried by the type. -/
def InitBefore {g : LoadGraph} (init : InitOrder g) (a b : Fin g.objects.size) : Prop :=
  ∃ ia ib : Nat,
    init.order[ia]? = some a ∧
    init.order[ib]? = some b ∧
    ia < ib

/-- Nat-index wrapper around `InitBefore`, useful when working from `g.Step`
    edges, whose endpoints are Nat-valued. Bounds are carried by the `Fin`
    entries inside `initOrder`; this wrapper intentionally compares their
    underlying natural indices. -/
def InitBeforeIdx {g : LoadGraph} (init : InitOrder g) (a b : Nat) : Prop :=
  LoadGraph.PostBefore (init.order.map (fun ix => ix.val)) a b

/-- Every object index appears in `init.order`. Bounds are carried by the `Fin`
    entries; this predicate names the coverage half of the init-order
    permutation witness. -/
def Covers {g : LoadGraph} (init : InitOrder g) : Prop :=
  ∀ i, i < g.objects.size → i ∈ (init.order.map (fun ix => ix.val)).toList

/-- Init-order topological property for produced graphs.

    For a direct dependency edge `i → j`, the dependency `j` appears before its
    dependent `i`. Discover rejects active-stack cycles while building the graph;
    gabi 08 leaves cyclic init ordering undefined. -/
def RespectsDeps {g : LoadGraph} (init : InitOrder g) : Prop :=
  ∀ i j, g.Step i j → init.InitBeforeIdx j i

theorem covers_spec {g : LoadGraph} (init : InitOrder g) :
    init.Covers :=
  init.covers

theorem respectsDeps_spec {g : LoadGraph} (init : InitOrder g) :
    init.RespectsDeps := by
  intro i j h_step
  exact init.respectsDeps i j h_step

/-- Every value in an `InitOrder` is a valid object index. -/
theorem mem_lt_objects {g : LoadGraph} (init : InitOrder g) {i : Nat}
    (h_mem : i ∈ (init.order.map (fun ix => ix.val)).toList) :
    i < g.objects.size := by
  rw [Array.toList_map] at h_mem
  rw [List.mem_map] at h_mem
  rcases h_mem with ⟨ix, _h_ix_mem, h_eq⟩
  rw [← h_eq]
  exact ix.isLt

/-- `InitOrder.covers` plus Fin-typed entries characterises order membership. -/
theorem mem_iff_lt_objects {g : LoadGraph} (init : InitOrder g) {i : Nat} :
    i ∈ (init.order.map (fun ix => ix.val)).toList ↔ i < g.objects.size := by
  constructor
  · exact init.mem_lt_objects
  · intro h_lt
    exact init.covers i h_lt

/-- A duplicate-free init order cannot put one index before itself. -/
theorem InitBeforeIdx.ne {g : LoadGraph} (init : InitOrder g) {a b : Nat}
    (h : init.InitBeforeIdx a b) : a ≠ b := by
  exact LoadGraph.PostBefore.ne_of_nodup
    (by simpa [Array.toList_map] using init.nodup) h

/-- A duplicate-free init order cannot place `a` before `b` and `b` before `a`. -/
theorem InitBeforeIdx.not_reverse {g : LoadGraph} (init : InitOrder g) {a b : Nat}
    (h : init.InitBeforeIdx a b) : ¬ init.InitBeforeIdx b a := by
  exact LoadGraph.PostBefore.not_reverse_of_nodup
    (by simpa [Array.toList_map] using init.nodup) h

/-- A certified init order rules out direct self-dependencies. -/
theorem step_ne {g : LoadGraph} (init : InitOrder g) {i j : Nat}
    (h : g.Step i j) : j ≠ i := by
  exact InitBeforeIdx.ne init (init.respectsDeps_spec i j h)

/-- A certified init order rules out direct two-node dependency cycles. -/
theorem step_not_reverse {g : LoadGraph} (init : InitOrder g) {i j : Nat}
    (h : g.Step i j) : ¬ g.Step j i := by
  have h_before := init.respectsDeps_spec i j h
  intro h_rev
  exact InitBeforeIdx.not_reverse init h_before (init.respectsDeps_spec j i h_rev)

end InitOrder

/-- Public Discover result: the dependency graph plus the init schedule derived
    from that graph. Keeping the schedule here (rather than inside `LoadGraph`)
    makes graph identity just objects + dependency edges. -/
structure Result where
  graph : LoadGraph
  initOrder : InitOrder graph
  deriving Repr

end LeanLoad.Discover

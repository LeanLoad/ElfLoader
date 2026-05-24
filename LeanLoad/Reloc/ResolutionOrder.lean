/-
BFS traversal of the dep graph for symbol resolution.

Spec: gabi 08 § Shared Object Dependencies — "the dynamic linker
examines the symbol tables with a breadth-first search. … first
looks at the symbol table of the executable program itself, then at
the symbol tables of the `DT_NEEDED` entries (in order), and then
at the second level `DT_NEEDED` entries, and so on."

This file produces that order as a pure data computation on
`LoadGraph`. `Discover`'s own traversal order is irrelevant — the
graph is the graph, and BFS is a derived view.

Three observables:

  • `bfsOrder g` — the BFS-order array of `Fin g.objects.size`.
  • `bfsOrder_nodup` — every entry appears at most once.
  • `bfsOrder_head`  — main (`⟨0, sizePos⟩`) is the first entry.

Both observables factor through `BfsInv`, the (seen, queue, order)
invariant `bfsLoop` maintains: `seen = order ++ queue`, `seen` is
`Nodup`, and every seen node is reachable from main. Nodes are marked
seen when enqueued, not when popped, so the queue never carries duplicates.

Fuel-bounded for Lean termination; enqueue-time marking means each loop
iteration consumes one distinct object, so `objects.size` fuel is enough.
-/

import LeanLoad.Discover.Graph

namespace LeanLoad.Reloc

open LeanLoad
open LeanLoad.Discover (LoadGraph)

/-- Object index in `g.objects`. -/
private abbrev ObjectIdx (g : LoadGraph) := Fin g.objects.size

/-- Out-neighbors of `idx`, lifted from raw `Nat` dependency entries into
    total object indices. -/
private def children (g : LoadGraph) (idx : ObjectIdx g) : List (ObjectIdx g) :=
  have h_lt_deps : idx.val < g.deps.size := by
    rw [g.depsSize]; exact idx.isLt
  (g.deps[idx.val]'h_lt_deps).attach.toList.map fun ⟨c, h_mem⟩ =>
    ⟨c, g.depsBounds idx.val h_lt_deps c h_mem⟩

/-- Membership in `children` is exactly a dependency step from the parent. -/
private theorem child_step (g : LoadGraph) {idx child : ObjectIdx g}
    (h_child : child ∈ children g idx) : g.Step idx.val child.val := by
  unfold children at h_child
  rw [List.mem_map] at h_child
  obtain ⟨⟨c, h_mem⟩, _h_attach, h_eq⟩ := h_child
  refine ⟨by rw [g.depsSize]; exact idx.isLt, ?_⟩
  rw [← h_eq]
  exact h_mem

/-- Reachability propagates across one child edge. -/
private theorem child_reachable (g : LoadGraph) {idx child : ObjectIdx g}
    (h_idx : g.ReachableFromMain idx.val) (h_child : child ∈ children g idx) :
    g.ReachableFromMain child.val := by
  unfold LoadGraph.ReachableFromMain at *
  exact LoadGraph.Reachable.tail h_idx (child_step g h_child)

/-- Queue state for BFS. `seen` is the set-as-list of nodes discovered so far:
    processed nodes in `order` plus pending nodes in `queue`. -/
private structure BfsState (g : LoadGraph) where
  queue : List (ObjectIdx g)
  seen  : List (ObjectIdx g)
  order : Array (ObjectIdx g)
  deriving Repr

namespace BfsState

/-- Initial BFS state: main is discovered and pending. -/
private def init (g : LoadGraph) : BfsState g :=
  let main : ObjectIdx g := ⟨0, g.sizePos⟩
  { queue := [main], seen := [main], order := #[] }

end BfsState

/-- Append fresh children to the queue, marking them seen at enqueue time. -/
private def enqueueFresh {g : LoadGraph}
    (xs : List (ObjectIdx g)) (state : BfsState g) : BfsState g :=
  match xs with
  | [] => state
  | child :: rest =>
      if child ∈ state.seen then
        enqueueFresh rest state
      else
        enqueueFresh rest
          { state with
            seen := state.seen ++ [child]
            queue := state.queue ++ [child] }

/-- Enqueueing does not alter the processed order. -/
private theorem enqueueFresh_order {g : LoadGraph} :
    ∀ (xs : List (ObjectIdx g)) (state : BfsState g),
      (enqueueFresh xs state).order = state.order := by
  intro xs
  induction xs with
  | nil =>
      intro state
      unfold enqueueFresh
      rfl
  | cons child rest ih =>
      intro state
      unfold enqueueFresh
      by_cases h_seen : child ∈ state.seen
      · simp [h_seen, ih]
      · simp [h_seen, ih]

private def bfsLoop (g : LoadGraph) (fuel : Nat) (state : BfsState g) :
    BfsState g :=
  match fuel with
  | 0 => state
  | fuel + 1 =>
      match state.queue with
      | [] => state
      | idx :: rest =>
          let processed : BfsState g :=
            { state with queue := rest, order := state.order.push idx }
          bfsLoop g fuel (enqueueFresh (children g idx) processed)
termination_by fuel

/-- BFS traversal of the dep graph starting at idx 0 (main). The
    returned array is the iteration order for `resolveByName` — every
    entry is in `[0, g.objects.size)` and the seen list ensures each
    index is enqueued at most once.

    Fuel = `objects.size`: each loop iteration pops one queue entry, and
    enqueue-time seen marking keeps the queue duplicate-free. -/
def bfsOrder (g : LoadGraph) : Array (Fin g.objects.size) :=
  (bfsLoop g g.objects.size (BfsState.init g)).order

-- ============================================================================
-- bfsOrder correctness witnesses: Nodup, reachability, and main-at-head.
-- These factor through an invariant on (seen, queue, order). Marking nodes
-- seen at enqueue time makes `seen = order.toList ++ queue` the central fact.
-- ============================================================================

/-- The invariant `bfsLoop` maintains on its mutable state. -/
private structure BfsInv (g : LoadGraph) (state : BfsState g) : Prop where
  /-- Seen nodes are exactly processed nodes followed by pending queue nodes. -/
  seen_eq : state.seen = state.order.toList ++ state.queue
  /-- No object index is seen twice (treated extensionally via `.val`). -/
  nodup : (state.seen.map (·.val)).Nodup
  /-- Every discovered node is reachable from main. -/
  reachable : ∀ x ∈ state.seen, g.ReachableFromMain x.val

/-- The initial bfs state — main pending, empty processed order — satisfies
    the invariant. -/
private theorem BfsInv.init (g : LoadGraph) :
    BfsInv g (BfsState.init g) :=
  { seen_eq := by simp [BfsState.init]
    nodup := by simp [BfsState.init]
    reachable := by
      intro x h_mem
      have h_eq : x = (⟨0, g.sizePos⟩ : ObjectIdx g) := by
        simpa [BfsState.init] using h_mem
      rw [h_eq]
      unfold LoadGraph.ReachableFromMain
      exact LoadGraph.Reachable.refl (g := g) 0 }

/-- Moving the queue head into `order` preserves the invariant before any
    children are enqueued. -/
private theorem BfsInv.processHead {g : LoadGraph} {idx : ObjectIdx g}
    {rest : List (ObjectIdx g)} {seen : List (ObjectIdx g)}
    {order : Array (ObjectIdx g)}
    (h_inv : BfsInv g { queue := idx :: rest, seen := seen, order := order }) :
    BfsInv g { queue := rest, seen := seen, order := order.push idx } :=
  { seen_eq := by
      change seen = (order.push idx).toList ++ rest
      have h_seen_eq : seen = order.toList ++ (idx :: rest) := h_inv.seen_eq
      rw [h_seen_eq, Array.toList_push]
      simp [List.append_assoc]
    nodup := h_inv.nodup
    reachable := h_inv.reachable }

/-- Enqueueing fresh reachable children preserves the central BFS invariant. -/
private theorem enqueueFresh_preserves_inv {g : LoadGraph} :
    ∀ (xs : List (ObjectIdx g)) (state : BfsState g),
      BfsInv g state →
      (∀ x ∈ xs, g.ReachableFromMain x.val) →
      BfsInv g (enqueueFresh xs state) := by
  intro xs
  induction xs with
  | nil =>
      intro state h_inv _h_reach
      unfold enqueueFresh
      exact h_inv
  | cons child rest ih =>
      intro state h_inv h_reach
      unfold enqueueFresh
      by_cases h_seen : child ∈ state.seen
      · simp [h_seen]
        exact ih state h_inv (by
          intro x h_x
          exact h_reach x (by simp [h_x]))
      · simp [h_seen]
        apply ih
        · have h_child_reach : g.ReachableFromMain child.val :=
            h_reach child (by simp)
          have h_val_not : child.val ∉ state.seen.map (fun x => x.val) := by
            intro h_val_mem
            rw [List.mem_map] at h_val_mem
            obtain ⟨x, h_x_mem, h_x_val⟩ := h_val_mem
            have h_x_eq : x = child := Fin.ext h_x_val
            rw [h_x_eq] at h_x_mem
            exact h_seen h_x_mem
          exact
            { seen_eq := by
                dsimp
                rw [h_inv.seen_eq]
                simp [List.append_assoc]
              nodup := by
                dsimp
                rw [List.map_append, List.map_singleton, List.nodup_append]
                refine ⟨h_inv.nodup, by simp, ?_⟩
                intro a h_a b h_b h_eq
                rw [List.mem_singleton] at h_b
                subst h_b
                exact h_val_not (by simpa [h_eq] using h_a)
              reachable := by
                intro x h_x
                dsimp at h_x
                rw [List.mem_append, List.mem_singleton] at h_x
                rcases h_x with h_old | h_eq
                · exact h_inv.reachable x h_old
                · rw [h_eq]
                  exact h_child_reach }
        · intro x h_x
          exact h_reach x (by simp [h_x])

/-- `bfsLoop` preserves the `BfsInv` invariant. The recursive cases:
    · empty queue → return state unchanged.
    · nonempty queue → move the head to `order`; append only fresh children to
      the queue, marking them seen immediately. -/
private theorem bfsLoop_preserves_inv (g : LoadGraph) (fuel : Nat) :
    ∀ state : BfsState g,
      BfsInv g state →
      BfsInv g (bfsLoop g fuel state) := by
  induction fuel with
  | zero =>
      intro state h_inv
      unfold bfsLoop
      exact h_inv
  | succ fuel ih =>
      intro state h_inv
      cases state with
      | mk queue seen order =>
      unfold bfsLoop
      cases queue with
      | nil =>
          exact h_inv
      | cons idx rest =>
          have h_idx_reach : g.ReachableFromMain idx.val :=
            h_inv.reachable idx (by
              rw [h_inv.seen_eq]
              simp)
          apply ih
          apply enqueueFresh_preserves_inv
          · exact BfsInv.processHead h_inv
          · intro child h_child
            exact child_reachable g h_idx_reach h_child

/-- The final state produced by `bfsOrder` satisfies the BFS invariant. -/
private theorem bfsOrder_inv (g : LoadGraph) :
    BfsInv g (bfsLoop g g.objects.size (BfsState.init g)) :=
  bfsLoop_preserves_inv g g.objects.size (BfsState.init g) (BfsInv.init g)

/-- `bfsOrder` has no duplicate indices. Combined with the `Fin
    g.objects.size` typing, it makes `bfsOrder` an injection into the
    object index space — every reachable object appears at most once. -/
theorem bfsOrder_nodup (g : LoadGraph) :
    ((bfsOrder g).toList.map (·.val)).Nodup := by
  unfold bfsOrder
  let final := bfsLoop g g.objects.size (BfsState.init g)
  change (final.order.toList.map (fun x => x.val)).Nodup
  have h_inv : BfsInv g final := bfsOrder_inv g
  have h_seen := h_inv.nodup
  rw [h_inv.seen_eq, List.map_append, List.nodup_append] at h_seen
  exact h_seen.1

/-- Every entry in `bfsOrder` is reachable from main in the discovered
    dependency graph. -/
theorem bfsOrder_reachable (g : LoadGraph) {i : Fin g.objects.size}
    (h_mem : i ∈ (bfsOrder g).toList) :
    g.ReachableFromMain i.val := by
  unfold bfsOrder at h_mem
  let final := bfsLoop g g.objects.size (BfsState.init g)
  change i ∈ final.order.toList at h_mem
  have h_inv : BfsInv g final := bfsOrder_inv g
  have h_seen_mem : i ∈ final.seen := by
    rw [h_inv.seen_eq, List.mem_append]
    exact Or.inl h_mem
  exact h_inv.reachable i h_seen_mem

/-- `bfsLoop`'s output `toList` is `state.order.toList` followed by some
    appended tail — prior entries are preserved at their positions, and the
    recursion only appends. -/
private theorem bfsLoop_toList_prefix (g : LoadGraph) (fuel : Nat) :
    ∀ state : BfsState g,
      ∃ suffix : List (Fin g.objects.size),
        (bfsLoop g fuel state).order.toList = state.order.toList ++ suffix := by
  induction fuel with
  | zero =>
      intro state
      refine ⟨[], ?_⟩
      unfold bfsLoop
      simp
  | succ fuel ih =>
      intro state
      cases state with
      | mk queue seen order =>
      unfold bfsLoop
      cases queue with
      | nil => exact ⟨[], by simp⟩
      | cons idx rest =>
          obtain ⟨subSuffix, h_sub⟩ := ih
            (enqueueFresh (children g idx)
              { queue := rest, seen := seen, order := order.push idx })
          refine ⟨idx :: subSuffix, ?_⟩
          rw [h_sub, enqueueFresh_order, Array.toList_push]
          simp [List.append_assoc]

/-- Main is the first entry in `bfsOrder`. Unfolds one iteration:
    process `⟨0, sizePos⟩`, then use `bfsLoop_toList_prefix` to lift
    the head through the remaining iterations. -/
private theorem bfsLoop_init_head (g : LoadGraph) {fuel : Nat} (h_fuel : 0 < fuel) :
    ((bfsLoop g fuel (BfsState.init g)).order)[0]? = some ⟨0, g.sizePos⟩ := by
  cases fuel with
  | zero => exact False.elim (Nat.not_lt_zero 0 h_fuel)
  | succ fuel =>
  let main : Fin g.objects.size := ⟨0, g.sizePos⟩
  change ((bfsLoop g (Nat.succ fuel) (BfsState.init g)).order)[0]? = some main
  unfold bfsLoop BfsState.init
  obtain ⟨suffix, h_suffix⟩ := bfsLoop_toList_prefix g
    fuel
    (enqueueFresh (children g main)
      { queue := [], seen := [main], order := (#[] : Array (Fin g.objects.size)).push main })
  rw [← Array.getElem?_toList, h_suffix]
  rw [enqueueFresh_order, Array.toList_push]
  show ([main] ++ suffix)[0]? = some main
  rfl

theorem bfsOrder_head (g : LoadGraph) :
    (bfsOrder g)[0]? = some ⟨0, g.sizePos⟩ := by
  unfold bfsOrder
  exact bfsLoop_init_head g g.sizePos

-- ============================================================================
-- Deferred theorems on `bfsOrder` (spec witnesses for gabi 08).
--
-- Each statement below is well-typed against the definitions above
-- (`bfsOrder`, `g.Step`, `g.Reachable`, `g.ReachableFromMain`); the
-- proofs are non-trivial without further machinery and are deferred.
-- The shapes are documented here so future work can fill in the proofs
-- without revisiting the spec.
--
-- ---- bfsOrder_complete (no missed matches) ----
--
--   theorem bfsOrder_complete (g : LoadGraph) (i : Fin g.objects.size)
--       (h : g.ReachableFromMain i.val) :
--       i ∈ (bfsOrder g).toList
--
-- Says: every index reachable from main via `g.deps` appears in the
-- BFS order. Combined with `resolveByName_is_bfs`, this gives "no
-- missed matches": if some reachable elf defines a symbol, the
-- iteration over `bfsOrder` will find it.
--
-- ---- bfsOrder_size_eq_objects_size ----
--
--   theorem bfsOrder_size_eq_objects_size (g : LoadGraph)
--       (h : ∀ (i : Nat) (h_i : i < g.objects.size), g.ReachableFromMain i) :
--       (bfsOrder g).size = g.objects.size
--
-- Follows from `bfsOrder_nodup` + `bfsOrder_complete` + the
-- "everything-is-reachable" property of `Discover.discover`.
-- Combined with Nodup makes `bfsOrder` a permutation of
-- `Fin g.objects.size`.
--
-- ---- bfsOrder_distance_monotone (the full gabi-08 BFS witness) ----
--
--   theorem bfsOrder_distance_monotone (g : LoadGraph) :
--       ∀ (i j : Nat) (h_i : i < (bfsOrder g).size)
--         (h_j : j < (bfsOrder g).size),
--         i ≤ j → bfsDistance g (bfsOrder g)[i] ≤ bfsDistance g (bfsOrder g)[j]
--
-- "Positions in bfsOrder are non-decreasing in BFS distance from
-- main." This is the precise formal version of the gabi-08 spec
-- ("first looks at main, then DT_NEEDED entries in order, then
-- second-level..."). Needs a queue invariant: "all queue elements
-- have distance d or d+1 from main, and visited has all distance <d
-- elements".
-- ============================================================================

end LeanLoad.Reloc

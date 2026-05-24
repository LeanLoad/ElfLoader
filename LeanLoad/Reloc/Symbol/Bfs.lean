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

Both observables factor through `BfsInv`, the (visited, order)
invariant `bfsLoop` maintains: `order` is `Nodup`, and every entry
in `order` is marked visited. The freshness check `visited[idx]`
before pushing prevents Nodup violations.

Fuel-bounded for Lean termination; the bound
`totalEdges + objects.size + 1` is provably sufficient for the
queue to empty.
-/

import LeanLoad.Discover.Graph

namespace LeanLoad.Reloc.Symbol

open LeanLoad
open LeanLoad.Discover (LoadGraph)

private def bfsLoop (g : LoadGraph) (fuel : Nat)
    (queue : List (Fin g.objects.size))
    (visited : Vector Bool g.objects.size)
    (order : Array (Fin g.objects.size)) :
    Array (Fin g.objects.size) :=
  match fuel with
  | 0 => order
  | fuel + 1 =>
    match queue with
    | [] => order
    | idx :: rest =>
      match visited[idx] with
      | true => bfsLoop g fuel rest visited order
      | false =>
        let visited' := visited.set idx.val true idx.isLt
        let order' := order.push idx
        have h_lt_deps : idx.val < g.deps.size := by
          rw [g.depsSize]; exact idx.isLt
        let children : List (Fin g.objects.size) :=
          (g.deps[idx.val]'h_lt_deps).attach.toList.map fun ⟨c, h_mem⟩ =>
            ⟨c, g.depsBounds idx.val h_lt_deps c h_mem⟩
        bfsLoop g fuel (rest ++ children) visited' order'
termination_by fuel

/-- Total number of edges in the dep graph — sum over objects of
    `deps[i].size`. Bounds the number of `bfsLoop` iterations needed
    for completeness (each iteration either pops one queue element,
    and each push is one out-edge from a newly-visited node). -/
def totalEdges (g : LoadGraph) : Nat :=
  g.deps.foldl (fun acc r => acc + r.size) 0

/-- BFS traversal of the dep graph starting at idx 0 (main). The
    returned array is the iteration order for `resolveByName` — every
    entry is in `[0, g.objects.size)` (by `g.depsBounds`) and the
    visited bitmap ensures each index is visited at most once.

    Fuel = `totalEdges + objects.size + 1` is provably sufficient
    for the queue to empty: each iteration pops one element, and the
    total push count is bounded by `1 + totalEdges` (initial main
    push plus one push per out-edge from a visited node). The `+n`
    slack accommodates the visited-bitmap bound. -/
def bfsOrder (g : LoadGraph) : Array (Fin g.objects.size) :=
  bfsLoop g (totalEdges g + g.objects.size + 1)
    [⟨0, g.sizePos⟩] (Vector.replicate _ false) #[]

-- ============================================================================
-- bfsOrder correctness witnesses: Nodup of indices + main-at-head.
-- These factor through an invariant on (visited, order) that bfsLoop
-- maintains across its recursion: order has no duplicates, and every
-- entry in order is marked visited. The freshness check `visited[idx]`
-- before pushing prevents Nodup violations.
-- ============================================================================

/-- The invariant `bfsLoop` maintains on its mutable state. -/
private structure BfsInv (g : LoadGraph)
    (visited : Vector Bool g.objects.size)
    (order : Array (Fin g.objects.size)) : Prop where
  /-- `order` has no duplicate indices (treated as `Nat` via `.val`). -/
  nodup : (order.toList.map (·.val)).Nodup
  /-- Every entry in `order` is marked visited — the contrapositive
      (idx not visited ⇒ idx not in order) is what `bfsLoop`'s
      else-branch uses to extend `order` while keeping Nodup. -/
  orderVisited : ∀ x ∈ order.toList, visited[x] = true

/-- The initial bfs state — empty order, no visited — satisfies the invariant. -/
private theorem BfsInv.init (g : LoadGraph) :
    BfsInv g (Vector.replicate g.objects.size false) #[] :=
  { nodup := by simp
    orderVisited := by intro x h; simp at h }

/-- `bfsLoop` preserves the `BfsInv` invariant. The recursive cases:
    · empty queue → return order unchanged. Invariant trivially preserved.
    · visited head → recurse with same state. Invariant preserved.
    · unvisited head → push to order + mark visited + recurse. Invariant
      preserved because the pushed index was *fresh* (visited was false,
      so by `orderVisited` contrapositive, the index wasn't already in
      order). -/
private theorem bfsLoop_preserves_inv (g : LoadGraph) (fuel : Nat) :
    ∀ (queue : List (Fin g.objects.size))
      (visited : Vector Bool g.objects.size)
      (order : Array (Fin g.objects.size)),
      BfsInv g visited order →
      ((bfsLoop g fuel queue visited order).toList.map (·.val)).Nodup := by
  induction fuel with
  | zero =>
    intro queue visited order h_inv
    show ((bfsLoop g 0 queue visited order).toList.map (·.val)).Nodup
    unfold bfsLoop
    exact h_inv.nodup
  | succ fuel ih =>
    intro queue visited order h_inv
    unfold bfsLoop
    cases queue with
    | nil => exact h_inv.nodup
    | cons idx rest =>
      simp only
      by_cases h_vidx : visited[idx] = true
      · -- visited[idx] = true: skip, state unchanged.
        rw [h_vidx]
        exact ih rest visited order h_inv
      · -- visited[idx] = false: push idx + mark visited + recurse.
        have h_vidx_false : visited[idx] = false := by
          cases h_b : visited[idx] with
          | true => exact absurd h_b h_vidx
          | false => rfl
        rw [h_vidx_false]
        -- Establish idx ∉ order.toList (to preserve Nodup after push).
        have h_idx_not_in : idx ∉ order.toList := fun h_mem => by
          have := h_inv.orderVisited idx h_mem
          rw [h_vidx_false] at this
          exact Bool.noConfusion this
        -- Build the new invariant.
        have h_inv' : BfsInv g (visited.set idx.val true idx.isLt) (order.push idx) :=
          { nodup := by
              rw [Array.toList_push, List.map_append, List.map_singleton]
              rw [List.nodup_append]
              refine ⟨h_inv.nodup, by simp, ?_⟩
              intro a h_a b h_b h_eq
              rw [List.mem_singleton] at h_b
              subst h_b
              -- a ∈ order.toList.map (·.val), a = idx.val. Contradicts h_idx_not_in.
              rw [List.mem_map] at h_a
              obtain ⟨x, h_x_mem, h_x_val⟩ := h_a
              -- x ∈ order.toList, x.val = a = idx.val → x = idx (Fin proof-irrel).
              have h_x_eq : x = idx := Fin.ext (h_x_val.trans h_eq)
              subst h_x_eq
              exact h_idx_not_in h_x_mem
            orderVisited := by
              intro x h_mem
              rw [Array.toList_push, List.mem_append, List.mem_singleton] at h_mem
              show (visited.set idx.val true idx.isLt)[x] = true
              rcases h_mem with h_old | h_eq
              · -- x ∈ old order. By orderVisited: visited[x] = true.
                have h_old_vis := h_inv.orderVisited x h_old
                show (visited.set idx.val true idx.isLt)[x.val]'x.isLt = true
                rw [Vector.getElem_set]
                split
                · rfl
                · exact h_old_vis
              · -- x = idx. visited'[idx] = true after the set.
                subst h_eq
                show (visited.set x.val true x.isLt)[x.val]'x.isLt = true
                rw [Vector.getElem_set]
                simp }
        -- Apply IH to the recursive call.
        exact ih _ _ _ h_inv'

/-- `bfsOrder` has no duplicate indices. Combined with the `Fin
    g.objects.size` typing, it makes `bfsOrder` an injection into the
    object index space — every reachable object appears at most once. -/
theorem bfsOrder_nodup (g : LoadGraph) :
    ((bfsOrder g).toList.map (·.val)).Nodup :=
  bfsLoop_preserves_inv g _ _ _ _ (BfsInv.init g)

/-- `bfsLoop`'s output `toList` is `order.toList` followed by some
    appended tail — prior entries are preserved at their positions,
    and the recursion only appends. -/
private theorem bfsLoop_toList_prefix (g : LoadGraph) (fuel : Nat) :
    ∀ (queue : List (Fin g.objects.size))
      (visited : Vector Bool g.objects.size)
      (order : Array (Fin g.objects.size)),
      ∃ suffix : List (Fin g.objects.size),
        (bfsLoop g fuel queue visited order).toList = order.toList ++ suffix := by
  induction fuel with
  | zero =>
    intro queue visited order
    refine ⟨[], ?_⟩
    show (bfsLoop g 0 queue visited order).toList = order.toList ++ []
    unfold bfsLoop
    simp
  | succ fuel ih =>
    intro queue visited order
    unfold bfsLoop
    cases queue with
    | nil => exact ⟨[], by simp⟩
    | cons idx rest =>
      simp only
      by_cases h_vidx : visited[idx] = true
      · rw [h_vidx]
        exact ih rest visited order
      · have h_vidx_false : visited[idx] = false := by
          cases h_b : visited[idx] with
          | true => exact absurd h_b h_vidx
          | false => rfl
        rw [h_vidx_false]
        -- After push, recurse on `order.push idx`. Result's toList equals
        -- (order.push idx).toList ++ subSuffix = order.toList ++ [idx] ++ subSuffix.
        obtain ⟨subSuffix, h_sub⟩ := ih _ _ (order.push idx)
        refine ⟨idx :: subSuffix, ?_⟩
        rw [h_sub, Array.toList_push]
        simp

/-- Main is the first entry in `bfsOrder`. Unfolds one iteration:
    push `⟨0, sizePos⟩` since `visited[0] = false`, then use
    `bfsLoop_toList_prefix` to lift the head through the recursion. -/
theorem bfsOrder_head (g : LoadGraph) :
    (bfsOrder g)[0]? = some ⟨0, g.sizePos⟩ := by
  have h_vis_main :
      (Vector.replicate g.objects.size false)[(⟨0, g.sizePos⟩ : Fin g.objects.size)]
        = false := by
    show (Vector.replicate g.objects.size false)[0]'g.sizePos = false
    simp
  -- After unfolding one iteration, the recursive call has
  -- `order = #[⟨0, sizePos⟩]`. `bfsLoop_toList_prefix` lifts that
  -- head through the remaining iterations.
  have h_step : bfsOrder g =
      bfsLoop g (totalEdges g + g.objects.size)
        ([] ++ ((g.deps[(⟨0, g.sizePos⟩ : Fin g.objects.size).val]'(by
                  rw [g.depsSize]; exact g.sizePos)).attach.toList.map fun ⟨c, h_mem⟩ =>
                (⟨c, g.depsBounds (⟨0, g.sizePos⟩ : Fin g.objects.size).val
                    (by rw [g.depsSize]; exact g.sizePos) c h_mem⟩
                  : Fin g.objects.size)))
        ((Vector.replicate g.objects.size false).set
          (⟨0, g.sizePos⟩ : Fin g.objects.size).val true
          (⟨0, g.sizePos⟩ : Fin g.objects.size).isLt)
        ((#[] : Array (Fin g.objects.size)).push ⟨0, g.sizePos⟩) := by
    show bfsLoop g (totalEdges g + g.objects.size + 1) _ _ _ = _
    rw [bfsLoop]
    simp [h_vis_main]
  rw [h_step]
  obtain ⟨suffix, h_suffix⟩ := bfsLoop_toList_prefix g
    (totalEdges g + g.objects.size)
    ([] ++ ((g.deps[(⟨0, g.sizePos⟩ : Fin g.objects.size).val]'(by
              rw [g.depsSize]; exact g.sizePos)).attach.toList.map fun ⟨c, h_mem⟩ =>
            (⟨c, g.depsBounds (⟨0, g.sizePos⟩ : Fin g.objects.size).val
                (by rw [g.depsSize]; exact g.sizePos) c h_mem⟩
              : Fin g.objects.size)))
    ((Vector.replicate g.objects.size false).set
      (⟨0, g.sizePos⟩ : Fin g.objects.size).val true
      (⟨0, g.sizePos⟩ : Fin g.objects.size).isLt)
    ((#[] : Array (Fin g.objects.size)).push ⟨0, g.sizePos⟩)
  rw [← Array.getElem?_toList, h_suffix]
  show ([⟨0, g.sizePos⟩] ++ suffix)[0]? = some ⟨0, g.sizePos⟩
  rfl

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

end LeanLoad.Reloc.Symbol

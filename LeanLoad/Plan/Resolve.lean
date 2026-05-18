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
`LoadGraph.objects` array (which `Discover` already returns in BFS
order: main first, then NEEDED entries in their declared order).

Each entry's resolution is one of three explicit cases:
  • `found ref` — the BFS turned up a defining (object, symbol).
  • `weakUndef` — undef reference is weak (gabi 05 lets it bind to 0).
  • `strongUndef` — undef reference is strong and would fail at load.

`missing` and `weakMissing` are derived projections over `entries`,
not separately maintained arrays — the inductive `Resolution` is the
single source of truth.
-/

import LeanLoad.Parse.RawDyn
import LeanLoad.Elaborate.Elf
import LeanLoad.Discover.Graph
import Std.Data.HashMap

namespace LeanLoad.Plan.Resolve

open LeanLoad
open LeanLoad.Parse
open LeanLoad.Elaborate
open LeanLoad.Discover (LoadGraph)

/-- A resolved global symbol, parameterised by the elf-array size `objCount`.
    The `Fin objCount` carries the bounds proof at the type level — every
    consumer indexes the elf array totally, no `?`. The `symIdx : Nat`
    stays unbounded because its valid range depends on the specific
    object referenced; consumers still `[]?` it. -/
structure SymRef (objCount : Nat) where
  objectIdx : Fin objCount
  symIdx    : Nat
  deriving Repr

/-- Look up `name` as a global definition in `elf`'s symbol table.
    Names are pre-resolved at validation time (see `Elaborate.Symbol`),
    so no string-table lookup happens here. -/
def findInElf (elf : Elaborate.Elf) (name : String) : Option Nat :=
  elf.symtab.findIdx? (fun entry => entry.isGlobalDef && entry.name == some name)

-- ============================================================================
-- bfsOrder — BFS traversal of (objects, deps) from idx 0. This is the
-- iteration order that gabi 08 § Shared Object Dependencies prescribes
-- for symbol resolution ("breadth-first search ... first looks at the
-- symbol table of the executable program itself, then at the symbol
-- tables of the DT_NEEDED entries (in order), and then at the second
-- level DT_NEEDED entries, and so on").
--
-- This is a pure data computation on `LoadGraph` — Discover's own
-- traversal order is irrelevant; the graph is the graph, and BFS is a
-- derived view. Fuel-bounded for Lean termination; the bound
-- `objects.size * (objects.size + 1) + 1` covers the worst case where
-- every object depends on every other.
-- ============================================================================

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
      if visited[idx] then
        bfsLoop g fuel rest visited order
      else
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
        rw [if_pos h_vidx]
        exact ih rest visited order h_inv
      · -- visited[idx] = false: push idx + mark visited + recurse.
        rw [if_neg h_vidx]
        -- The new state has visited' = visited.set idx true, order' = order.push idx.
        -- We need to show BfsInv for the new state.
        have h_vidx_false : visited[idx] = false := by
          cases h_b : visited[idx] with
          | true => exact absurd h_b h_vidx
          | false => rfl
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
      · rw [if_pos h_vidx]
        exact ih rest visited order
      · rw [if_neg h_vidx]
        -- After push, recurse on `order.push idx`. Result's toList equals
        -- (order.push idx).toList ++ subSuffix = order.toList ++ [idx] ++ subSuffix.
        obtain ⟨subSuffix, h_sub⟩ := ih _ _ (order.push idx)
        refine ⟨idx :: subSuffix, ?_⟩
        rw [h_sub, Array.toList_push]
        simp

-- ============================================================================
-- bfsOrder completeness: every reachable index appears in bfsOrder.
-- This is the "no missed matches" spec witness — combined with
-- `resolveByName_is_bfs`, it gives the gabi 08 § Shared Object
-- Dependencies completeness contract.
--
-- The proof uses a closed-under-step invariant on `(visited, queue)`:
-- once a node is visited, every step out of it lands somewhere we'll
-- still process (either already visited, or in the queue waiting).
-- Combined with fuel-sufficiency (each push exhausts at most one
-- bit of the visited bitmap; total pushes ≤ 1 + total deps edges),
-- the queue empties and every reachable node is in `order`.
--
-- For LoadGraph as produced by `Discover.discoverWith`: every object
-- is transitively-NEEDED from main, hence reachable. Combined with
-- `bfsOrder_complete`, `bfsOrder` is a permutation of `Fin
-- g.objects.size` — every loaded elf is tried during symbol lookup,
-- so `resolveByName` returns `none` iff truly no elf defines the
-- name.
-- ============================================================================

-- ============================================================================
-- Deferred theorems on `bfsOrder` (spec witnesses for gabi 08).
--
-- Each statement below is well-typed against the definitions above
-- (`bfsOrder`, `g.Step`, `g.Reachable`, `g.ReachableFromMain`); the
-- proofs are non-trivial without mathlib and are deferred. The
-- definitions are in place so future work can fill in the proofs
-- without revisiting the spec shape.
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
-- Proof strategy:
--   1. Strengthen `bfsOrder`'s fuel to `1 + ∑ |deps[i]|` (provably
--      sufficient — current `n*(n+1)+1` works for `|deps[i]| ≤ n`
--      but not for pathologically wide NEEDED lists).
--   2. Define a `BfsClosedInv g queue visited` invariant: for every
--      `i` with `visited[i] = true`, every step out of `i` lands in
--      `visited ∨ queue`.
--   3. Initial state (visited = ∅) satisfies the invariant vacuously.
--   4. `bfsLoop` preserves it: the unvisited-pop branch marks `idx`
--      visited *and* pushes all of `deps[idx]` to the queue, so the
--      newly-visited `idx`'s out-edges are accounted for.
--   5. At termination (queue empty + invariant), every reachable node
--      from main is visited. By induction on the `Reachable` path:
--        · refl case: `x = 0` is main, in the initial queue,
--          eventually visited.
--        · tail case `Reachable.tail h_i_j h_step`: by IH, `j ∈
--          visited ∪ queue`; with queue empty, `j ∈ visited`. By the
--          invariant, `k ∈ visited` too.
--   6. Specialize: `bfsOrder` is `bfsLoop` with the right initial
--      state and sufficient fuel, hence covers all reachable.
--
-- ~150 lines of BFS-correctness machinery without mathlib.
--
-- ---- bfsOrder_head ----
--
--   theorem bfsOrder_head (g : LoadGraph) :
--       (bfsOrder g)[0]? = some ⟨0, g.sizePos⟩
--
-- Main is always the first entry. Needs careful Bool-if elimination
-- on `(Vector.replicate _ false)[⟨0, sizePos⟩]` (doesn't reduce via
-- stock simp lemmas) or a small refactor of `bfsLoop` to use a
-- `match h : visited[idx]` form that exposes the equation. ~30 lines.
--
-- ---- bfsOrder_size_eq_objects_size ----
--
--   theorem bfsOrder_size_eq_objects_size (g : LoadGraph)
--       (h : ∀ (i : Nat) (h_i : i < g.objects.size), g.ReachableFromMain i) :
--       (bfsOrder g).size = g.objects.size
--
-- Follows from `bfsOrder_nodup` + `bfsOrder_complete` + the
-- "everything-is-reachable" property of `Discover.discoverWith` (the
-- hypothesis `h`, which would be either an 8th `LoadGraph` invariant
-- or a separate theorem on `discoverWith`'s output). The conclusion
-- combined with Nodup makes `bfsOrder` a permutation of `Fin
-- g.objects.size`.
--
-- ---- bfsOrder_distance_monotone (the full gabi-08 BFS witness) ----
--
--   def bfsDistance (g : LoadGraph) (i : Nat) : Nat :=
--     -- min d such that ∃ Reachable-path of length d from 0 to i.
--     ...
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
-- elements". ~100 lines on top of `bfsOrder_complete`.
-- ============================================================================

/-- Resolve `name` against the loaded graph via BFS-order traversal
    over `(g.objects, g.deps)`. The `order` argument is the BFS view
    (`bfsOrder g`); callers compute it once and reuse across many
    lookups (`buildTable`). Returns the providing `SymRef`, or `none`
    if no elf along `order` defines a matching global.

    Implemented via `Array.findSome?` so consumers can chain through
    the standard first-match characterisation lemmas
    (`resolveByName_provider_defines`, `resolveByName_is_bfs` below). -/
def resolveByName (g : LoadGraph) (order : Array (Fin g.objects.size))
    (name : String) : Option (SymRef g.objects.size) :=
  order.findSome? fun objectIdx =>
    (findInElf g.objects[objectIdx].elf name).map fun symIdx =>
      { objectIdx, symIdx }

/-- A failed-to-resolve undefined symbol; useful for diagnostics.
    Same `Fin objCount` parameterisation as `SymRef` so `Table.missing[i].objectIdx`
    is total. -/
structure Unresolved (objCount : Nat) where
  objectIdx : Fin objCount
  symIdx    : Nat
  name      : String
  deriving Repr

-- ============================================================================
-- Soundness theorems for `findInElf` and `resolveByName`. The
-- contract is gabi 08 § Shared Object Dependencies: BFS-first global
-- definition with the matching name. These theorems characterise the
-- public API in terms of that contract.
-- ============================================================================

/-- The predicate `findInElf` searches for. Made explicit so the
    `Array.findIdx?` characterisation lemmas can talk about it. -/
private def isMatchingDef (name : String) (entry : Symbol) : Bool :=
  entry.isGlobalDef && entry.name == some name

private theorem findInElf_eq_findIdx? (elf : Elaborate.Elf) (name : String) :
    findInElf elf name = elf.symtab.findIdx? (isMatchingDef name) :=
  rfl

/-- If `findInElf` returns `some symIdx`, the index is in bounds.
    Used as the size proof in `findInElf_provides` and
    `findInElf_is_first`. -/
theorem findInElf_lt_size {elf : Elaborate.Elf} {name : String} {symIdx : Nat}
    (h : findInElf elf name = some symIdx) : symIdx < elf.symtab.size := by
  rw [findInElf_eq_findIdx?, Array.findIdx?_eq_some_iff_getElem] at h
  exact h.1

/-- If `findInElf` returns `some symIdx`, the symbol at that index is
    a global definition with the matching name (gabi 08). The bound
    proof comes from `findInElf_lt_size`. -/
theorem findInElf_provides {elf : Elaborate.Elf} {name : String} {symIdx : Nat}
    (h : findInElf elf name = some symIdx) :
    (elf.symtab[symIdx]'(findInElf_lt_size h)).isGlobalDef = true ∧
    (elf.symtab[symIdx]'(findInElf_lt_size h)).name = some name := by
  have h' := h
  rw [findInElf_eq_findIdx?, Array.findIdx?_eq_some_iff_getElem] at h'
  obtain ⟨_h_lt, h_pred, _h_first⟩ := h'
  unfold isMatchingDef at h_pred
  rw [Bool.and_eq_true] at h_pred
  obtain ⟨h_def, h_name⟩ := h_pred
  exact ⟨h_def, beq_iff_eq.mp h_name⟩

/-- If `findInElf` returns `some symIdx`, every earlier symbol in the
    same elf is *not* a global definition with the matching name —
    `findIdx?`'s first-match property. -/
theorem findInElf_is_first {elf : Elaborate.Elf} {name : String} {symIdx : Nat}
    (h : findInElf elf name = some symIdx) (k : Nat) (h_k : k < symIdx) :
    ¬ ((elf.symtab[k]'(Nat.lt_trans h_k (findInElf_lt_size h))).isGlobalDef = true ∧
       (elf.symtab[k]'(Nat.lt_trans h_k (findInElf_lt_size h))).name = some name) := by
  intro ⟨h_def, h_name⟩
  rw [findInElf_eq_findIdx?, Array.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨_h_lt, _h_pred, h_first⟩ := h
  refine h_first k h_k ?_
  unfold isMatchingDef
  simp [h_def, h_name]

/-- If `resolveByName` returns `some ref`, `ref.symIdx` is in bounds
    for the providing elf's symtab. -/
theorem resolveByName_lt_size {g : LoadGraph}
    {order : Array (Fin g.objects.size)} {name : String}
    {ref : SymRef g.objects.size}
    (h : resolveByName g order name = some ref) :
    ref.symIdx < g.objects[ref.objectIdx].elf.symtab.size := by
  unfold resolveByName at h
  obtain ⟨idx, _h_mem, h_f⟩ := Array.exists_of_findSome?_eq_some h
  rw [Option.map_eq_some_iff] at h_f
  obtain ⟨symIdx, h_find, h_eq⟩ := h_f
  subst h_eq
  exact findInElf_lt_size h_find

/-- If `resolveByName` returns `some ref`, the symbol at `ref` is a
    global definition with the matching name. The gabi 08 BFS first-
    match contract is `resolveByName_is_bfs` below. -/
theorem resolveByName_provider_defines {g : LoadGraph}
    {order : Array (Fin g.objects.size)} {name : String}
    {ref : SymRef g.objects.size}
    (h : resolveByName g order name = some ref) :
    (g.objects[ref.objectIdx].elf.symtab[ref.symIdx]'(resolveByName_lt_size h)).isGlobalDef = true ∧
    (g.objects[ref.objectIdx].elf.symtab[ref.symIdx]'(resolveByName_lt_size h)).name
        = some name := by
  have h' := h
  unfold resolveByName at h'
  obtain ⟨idx, _h_mem, h_f⟩ := Array.exists_of_findSome?_eq_some h'
  rw [Option.map_eq_some_iff] at h_f
  obtain ⟨symIdx, h_find, h_eq⟩ := h_f
  subst h_eq
  exact findInElf_provides h_find

/-- First-match-along-`order` contract: the resolved provider is the
    first entry in `order` that defines a symbol with the matching
    name. Combined with `order = bfsOrder g`, this is the gabi 08
    § Shared Object Dependencies BFS-resolution contract.

    Stated abstractly over any `order` so it's a pure consequence of
    `Array.findSome?`'s first-match property. -/
theorem resolveByName_is_bfs {g : LoadGraph}
    {order : Array (Fin g.objects.size)} {name : String}
    {ref : SymRef g.objects.size}
    (h : resolveByName g order name = some ref) :
    ∃ (k : Nat) (h_k : k < order.size),
      order[k] = ref.objectIdx ∧
      ∀ (j : Nat) (h_j : j < k),
        findInElf
            (g.objects[order[j]'(Nat.lt_trans h_j h_k)]).elf
            name = none := by
  -- Decompose `findSome?` into prefix/match/suffix.
  unfold resolveByName at h
  rw [Array.findSome?_eq_some_iff] at h
  obtain ⟨ys, a, zs, h_split, h_f, h_first⟩ := h
  -- `a = ref.objectIdx` from `f a = some ref` (Option.map injective).
  rw [Option.map_eq_some_iff] at h_f
  obtain ⟨_symIdx, _h_findA, h_eq⟩ := h_f
  have h_obj_a : ref.objectIdx = a := by
    have := congrArg SymRef.objectIdx h_eq.symm; simpa using this
  -- The match position k = ys.size; bound from h_split.
  refine ⟨ys.size, ?_, ?_, ?_⟩
  · -- ys.size < order.size: from h_split, order = ys.push a ++ zs.
    have := congrArg Array.size h_split
    rw [Array.size_append, Array.size_push] at this
    omega
  · -- order[ys.size] = a = ref.objectIdx.
    have h_ys_lt_split : ys.size < (ys.push a ++ zs).size := by
      rw [Array.size_append, Array.size_push]; omega
    have h_get_split : (ys.push a ++ zs)[ys.size]'h_ys_lt_split = a := by
      rw [Array.getElem_append_left (hlt := by rw [Array.size_push]; omega),
          Array.getElem_push_eq]
    have h_order_get : order[ys.size]'(by
        rw [h_split, Array.size_append, Array.size_push]; omega) = a := by
      rw [show order[ys.size]'(by
            rw [h_split, Array.size_append, Array.size_push]; omega) =
          (ys.push a ++ zs)[ys.size]'h_ys_lt_split from
          by congr 1 <;> rw [h_split]]
      exact h_get_split
    rw [h_obj_a]; exact h_order_get
  · -- For j < ys.size: order[j] is in ys (prefix), so f order[j] = none
    -- by h_first.
    intro j h_j
    have h_j_lt_split : j < (ys.push a ++ zs).size := by
      rw [Array.size_append, Array.size_push]; omega
    have h_ys_get_split : (ys.push a ++ zs)[j]'h_j_lt_split = ys[j]'h_j := by
      rw [Array.getElem_append_left (hlt := by rw [Array.size_push]; omega),
          Array.getElem_push_lt h_j]
    have h_order_get : order[j]'(by
        rw [h_split, Array.size_append, Array.size_push]; omega) = ys[j]'h_j := by
      rw [show order[j]'(by
            rw [h_split, Array.size_append, Array.size_push]; omega) =
          (ys.push a ++ zs)[j]'h_j_lt_split from
          by congr 1 <;> rw [h_split]]
      exact h_ys_get_split
    have h_f_none := h_first _ (Array.getElem_mem h_j)
    rw [Option.map_eq_none_iff] at h_f_none
    -- `rw` would trip on the dependent proof of `order[j].val < objects.size`;
    -- rewrite the underlying Fin equality and let `simp` push it through.
    have h_objs_eq : g.objects[order[j]'(Nat.lt_trans h_j (by
        rw [h_split, Array.size_append, Array.size_push]; omega))]
        = g.objects[ys[j]'h_j] := by
      congr 1
    rw [h_objs_eq]
    exact h_f_none

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

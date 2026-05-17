/-
Init planner — base-free.

Produces a topological order over the discovered dep graph. gabi 08
mandates a *partial order* — "deps before dependents", cycle order
undefined. DFS post-order is *our* implementation choice (matches
glibc / musl); any valid topological sort would be conformant.
Reverse-BFS is *not* a valid topological sort on non-tree DAGs and
would violate the spec.

The dep edges live on `LoadGraph.deps` — recorded by Discover BFS at
edge-creation time, so the canonical-name dedup that converts
`DT_NEEDED libfoo.so` → loaded `libfoo.so.1` cannot drop edges
silently. `Init.order` just projects them and runs DFS post-order.

`order : (g : LoadGraph) → Array (Fin g.objects.size)` returns
Fin-indexed object indices so downstream consumers
(`Materialize.initAddrs`) can index `lp.elfs` and `bases` totally,
without `[]?`. The `Fin objCount` bound is preserved structurally through
DFS via the internal `DfsState objCount` carrier.

Address resolution (turn the order + bases + initArr into the flat
`Array UInt64` of ctor addresses to call) is base-aware and lives in
`Materialize.initAddrs`.
-/

import LeanLoad.Discover.Step
import LeanLoad.Elaborate.Elf

namespace LeanLoad.Plan.Init

open LeanLoad
open LeanLoad.Discover

-- ============================================================================
-- DFS post-order.
--
-- The `Fin objCount` bound on the produced order is preserved by carrying
-- `visited` as a `Vector Bool objCount`: every `push` into `order` is
-- guarded by `idx < objCount`, and `Vector.set` preserves the size at
-- the type level — no separate `visitedSize` proof field.
-- ============================================================================

/-- DFS carrier. Keeps the visited bitmap (sized to `objCount` at the
    type level via `Vector`) alongside the partial order. -/
private structure DfsState (objCount : Nat) where
  visited : Vector Bool objCount
  order   : Array (Fin objCount)

/-- Depth-first traversal helper. `visited[i]` marks an object that
    has either been emitted (`order` already contains it) or is
    currently in the descent path (cycle protection).

    `fuel` bounds the recursion depth. The caller seeds it with `objCount`
    (object count); each recursive call descends through one
    not-yet-visited object, so the bound is tight. With fuel, no
    `partial def` — `dfs` is structurally recursive. -/
private def dfs (fuel : Nat) (deps : Array (Array Nat)) (idx : Nat)
    (s : DfsState objCount) : DfsState objCount :=
  match fuel with
  | 0 => s
  | fuel + 1 =>
    if h : idx < objCount then
      if s.visited[idx] then s
      else
        let s' : DfsState objCount :=
          { visited := s.visited.set idx true, order := s.order }
        let children := (deps[idx]?).getD #[]
        let s'' := children.foldl (init := s') (fun st c => dfs fuel deps c st)
        { s'' with order := s''.order.push ⟨idx, h⟩ }
    else s
termination_by fuel

/-- Dependency order: depth-first post-order over `deps` from object 0
    (main). Init walks the result forward; fini walks it reversed. -/
def computeOrder (deps : Array (Array Nat)) (objCount : Nat) : Array (Fin objCount) :=
  if objCount == 0 then #[]
  else
    let s : DfsState objCount :=
      { visited := Vector.replicate objCount false
        order := Array.mkEmpty objCount }
    (dfs objCount deps 0 s).order

/-- Init order over an `LoadGraph`: project the BFS-recorded
    `g.deps` and run DFS post-order. The returned indices are typed
    `Fin g.objects.size` so downstream consumers can index `lp.elfs` /
    `bases` totally. -/
def order (g : LoadGraph) : Array (Fin g.objects.size) :=
  computeOrder g.deps g.objects.size

-- ============================================================================
-- Nodup proof. The proof structure:
--
--   1. `dfs_mono_subset` (combined): for any input state `s`, the
--      result `dfs fuel deps idx s` satisfies BOTH
--        (mono)   `s.visited[i] = true → result.visited[i] = true`, and
--        (subset) `i ∈ result.order → i ∈ s.order ∨ s.visited[i] = false`.
--      Bundling the two into one theorem lets the foldl-over-children
--      induction use a combined motive — each step's `dfs` IH
--      simultaneously gives mono-and-subset for that single call,
--      and the foldl invariant chains both. Proved by induction on
--      `fuel` + a `foldl_induction` over the children inside.
--
--   2. `Inv s` is `(every emitted index is visited) ∧ Nodup s.order`.
--      `dfs_preserves_inv` follows from (1): the `subset` half plus
--      the entry-condition `s.visited[idx] = false` rules out `idx`
--      already being in the children's-foldl output, so the push
--      preserves Nodup.
--
--   3. `Init.order_nodup` is `(3)` applied to the empty initial state.
-- ============================================================================

/-- Combined claim about a single `dfs` call:
    (mono) visited bits only flip false → true, AND
    (subset) every entry in the result's order was either in the input
    order or had its visited bit `false` at entry.

    Bundled because the foldl over children needs both at once. -/
private theorem dfs_mono_subset (fuel : Nat) (deps : Array (Array Nat))
    (idx : Nat) (s : DfsState objCount) :
    (∀ (i : Fin objCount), s.visited[i] = true →
      (dfs fuel deps idx s).visited[i] = true) ∧
    (∀ (i : Fin objCount), i ∈ (dfs fuel deps idx s).order →
      i ∈ s.order ∨ s.visited[i] = false) := by
  induction fuel generalizing idx s with
  | zero =>
    unfold dfs
    refine ⟨?_, ?_⟩
    · intro i h; exact h
    · intro i h_in; left; exact h_in
  | succ fuel ih =>
    unfold dfs
    split
    rotate_left
    · -- ¬ idx < objCount: dfs returns s
      refine ⟨?_, ?_⟩
      · intro i h; exact h
      · intro i h_in; left; exact h_in
    rename_i h_lt
    split
    · -- visited[idx] = true: dfs returns s
      refine ⟨?_, ?_⟩
      · intro i h; exact h
      · intro i h_in; left; exact h_in
    rename_i h_v
    -- After set, the post-set state s' has visited[idx] = true and
    -- visited[j] unchanged for j ≠ idx.
    let s' : DfsState objCount :=
      { visited := s.visited.set idx true, order := s.order }
    -- Closed form for s'.visited[j].
    have h_s'_get : ∀ (j : Fin objCount),
        s'.visited[j] = if idx = j.val then true else s.visited[j] := by
      intro j
      show (s.visited.set idx true)[j] = _
      exact Vector.getElem_set _ j.isLt
    have h_set_true : ∀ (j : Fin objCount), s.visited[j] = true →
        s'.visited[j] = true := by
      intro j h
      rw [h_s'_get]
      split
      · rfl
      · exact h
    have h_set_idx_was_false : ∀ (j : Fin objCount),
        s'.visited[j] = false → j.val ≠ idx := by
      intro j h_false h_eq
      rw [h_s'_get] at h_false
      simp [h_eq.symm] at h_false
    have h_set_unchanged : ∀ (j : Fin objCount),
        j.val ≠ idx → s'.visited[j] = s.visited[j] := by
      intro j h_ne
      rw [h_s'_get]
      exact if_neg (fun (h : idx = j.val) => h_ne h.symm)
    let children := (deps[idx]?).getD #[]
    -- Foldl induction with combined motive: from-s' mono + s-relative subset.
    let motive : Nat → DfsState objCount → Prop := fun _ st =>
      (∀ (j : Fin objCount), s'.visited[j] = true → st.visited[j] = true) ∧
      (∀ (j : Fin objCount), j ∈ st.order → j ∈ s.order ∨ s.visited[j] = false)
    have h_motive : motive children.size (children.foldl
        (init := s') (fun st c => dfs fuel deps c st)) := by
      refine Array.foldl_induction motive (init := s') ?_ ?_
      · -- Init: motive 0 s'.
        refine ⟨?_, ?_⟩
        · intro j h; exact h
        · intro j h_in
          -- s'.order = s.order
          left; exact h_in
      · -- Step: motive k st → motive (k+1) (dfs fuel deps c st).
        intro k st ih_st
        obtain ⟨ih_mono, ih_sub⟩ := ih_st
        have ih_dfs := ih (children[k.val]) st
        obtain ⟨h_dfs_mono, h_dfs_sub⟩ := ih_dfs
        refine ⟨?_, ?_⟩
        · -- Combined mono: s' → st → dfs ... .
          intro j h
          exact h_dfs_mono j (ih_mono j h)
        · -- Combined subset.
          intro j h_in
          rcases h_dfs_sub j h_in with h_in_st | h_unvis_st
          · exact ih_sub j h_in_st
          · -- st.visited[j] = false. Contrapositive of ih_mono:
            -- s'.visited[j] = false. Then j.val ≠ idx and s.visited[j] = false.
            right
            have h_s'_false : s'.visited[j] = false := by
              match h_v_eq : s'.visited[j] with
              | false => rfl
              | true =>
                have h_st_true := ih_mono j h_v_eq
                rw [h_unvis_st] at h_st_true; cases h_st_true
            have h_j_ne : j.val ≠ idx := h_set_idx_was_false j h_s'_false
            have h_unchanged := h_set_unchanged j h_j_ne
            rw [h_unchanged] at h_s'_false
            exact h_s'_false
    obtain ⟨h_final_mono, h_final_sub⟩ := h_motive
    -- Now derive both conjuncts for the full dfs result (after push).
    refine ⟨?_, ?_⟩
    · -- Mono of final = push doesn't touch visited.
      intro i h
      exact h_final_mono i (h_set_true i h)
    · -- Subset: result.order = s''.order.push ⟨idx, h_lt⟩.
      intro i h_in_push
      rcases Array.mem_push.mp h_in_push with h_in_s'' | h_eq
      · exact h_final_sub i h_in_s''
      · -- i = ⟨idx, h_lt⟩. s.visited[idx] = false from h_v.
        subst h_eq
        right
        exact (Bool.not_eq_true _).mp h_v

/-- Convenience: monotonicity alone, projected from the combined claim. -/
private theorem dfs_visited_mono (fuel : Nat) (deps : Array (Array Nat))
    (idx : Nat) (s : DfsState objCount) (i : Fin objCount)
    (h : s.visited[i] = true) :
    (dfs fuel deps idx s).visited[i] = true :=
  (dfs_mono_subset fuel deps idx s).1 i h

/-- Convenience: subset alone, projected from the combined claim. -/
private theorem dfs_order_subset (fuel : Nat) (deps : Array (Array Nat))
    (idx : Nat) (s : DfsState objCount) (i : Fin objCount)
    (h_new : i ∈ (dfs fuel deps idx s).order) :
    i ∈ s.order ∨ s.visited[i] = false :=
  (dfs_mono_subset fuel deps idx s).2 i h_new

/-- Foldl-version of mono+subset. Each step uses `dfs_mono_subset`;
    the foldl carries a combined motive that chains both. -/
private theorem foldl_dfs_mono_subset (fuel : Nat) (deps : Array (Array Nat))
    (children : Array Nat) (s : DfsState objCount) :
    (∀ (i : Fin objCount), s.visited[i] = true →
      (children.foldl (init := s) (fun st c => dfs fuel deps c st)).visited[i] = true) ∧
    (∀ (i : Fin objCount),
      i ∈ (children.foldl (init := s) (fun st c => dfs fuel deps c st)).order →
      i ∈ s.order ∨ s.visited[i] = false) := by
  refine Array.foldl_induction
    (motive := fun (_ : Nat) (st : DfsState objCount) =>
      (∀ (i : Fin objCount), s.visited[i] = true → st.visited[i] = true) ∧
      (∀ (i : Fin objCount), i ∈ st.order → i ∈ s.order ∨ s.visited[i] = false))
    ?_ ?_
  · refine ⟨?_, ?_⟩
    · intro i h; exact h
    · intro i h_in; left; exact h_in
  · intro k st ih_st
    obtain ⟨ih_mono, ih_sub⟩ := ih_st
    obtain ⟨dm, ds⟩ := dfs_mono_subset fuel deps children[k.val] st
    refine ⟨?_, ?_⟩
    · intro i h; exact dm i (ih_mono i h)
    · intro i h_in
      rcases ds i h_in with h_in_st | h_unvis_st
      · exact ih_sub i h_in_st
      · right
        match h_s_v : s.visited[i] with
        | false => rfl
        | true =>
          have := ih_mono i h_s_v
          rw [h_unvis_st] at this
          cases this

namespace DfsState

/-- Bundled invariant: every emitted index is currently visited, and
    the order has no duplicate `.val` projections.

    Stated element-wise (`∀ i ∈ s.order, …`) rather than index-wise
    (`∀ k h, … s.order[k]'h …`). The element-wise form avoids Lean's
    auto-generated bound-proof helpers, which otherwise block `rw`'s
    motive-finding on dependent `Vector + Fin` indexing. -/
def Inv (s : DfsState objCount) : Prop :=
  (∀ i ∈ s.order, s.visited[i] = true) ∧
  (s.order.toList.map (·.val)).Nodup

theorem Inv.empty (objCount : Nat) :
    Inv ({ visited := Vector.replicate objCount false,
           order := Array.mkEmpty objCount } : DfsState objCount) := by
  refine ⟨?_, ?_⟩
  · intro i h_in; simp at h_in
  · simp

end DfsState

/-- Main: `dfs` preserves the invariant. -/
private theorem dfs_preserves_inv (fuel : Nat) (deps : Array (Array Nat))
    (idx : Nat) (s : DfsState objCount) (h_inv : DfsState.Inv s) :
    DfsState.Inv (dfs fuel deps idx s) := by
  obtain ⟨h_visited, h_nodup⟩ := h_inv
  induction fuel generalizing idx s with
  | zero =>
    unfold dfs
    exact ⟨h_visited, h_nodup⟩
  | succ fuel ih =>
    unfold dfs
    split
    rotate_left
    · exact ⟨h_visited, h_nodup⟩
    rename_i h_lt
    split
    · exact ⟨h_visited, h_nodup⟩
    rename_i h_v
    -- s' = visited extended at idx; orderVisited preserved (set only adds true).
    let s' : DfsState objCount :=
      { visited := s.visited.set idx true, order := s.order }
    have h_s'_visited : ∀ i ∈ s'.order, s'.visited[i] = true := by
      intro i h_in
      -- i ∈ s'.order = s.order, so by h_visited s.visited[i] = true.
      -- After set, s'.visited[i] = true regardless of whether i.val = idx.
      have h_orig : s.visited[i] = true := h_visited i h_in
      show (s.visited.set idx true)[i] = true
      show (s.visited.set idx true)[i.val]'i.isLt = true
      rw [Vector.getElem_set]
      split
      · rfl
      · exact h_orig
    let children := (deps[idx]?).getD #[]
    -- Foldl preserves Inv via per-call ih.
    have h_foldl_inv : DfsState.Inv (children.foldl (init := s')
        (fun st c => dfs fuel deps c st)) := by
      refine Array.foldl_induction
        (motive := fun (_ : Nat) (st : DfsState objCount) => DfsState.Inv st)
        ?_ ?_
      · exact ⟨h_s'_visited, h_nodup⟩
      · intro k st ih_st
        obtain ⟨st_v, st_n⟩ := ih_st
        exact ih _ st st_v st_n
    obtain ⟨h_s''_v, h_s''_n⟩ := h_foldl_inv
    let s'' := children.foldl (init := s') (fun st c => dfs fuel deps c st)
    -- Foldl-relative subset: every j ∈ s''.order is in s'.order or
    -- had `s'.visited[j] = false` at the foldl's entry.
    have h_foldl_sub : ∀ j : Fin objCount, j ∈ s''.order →
        j ∈ s'.order ∨ s'.visited[j] = false :=
      (foldl_dfs_mono_subset fuel deps children s').2
    -- Push idx. Need: ⟨idx, h_lt⟩ ∉ s''.order (for Nodup).
    have h_idx_not_in_s'' : (⟨idx, h_lt⟩ : Fin objCount) ∉ s''.order := by
      intro h_mem
      rcases h_foldl_sub (⟨idx, h_lt⟩ : Fin objCount) h_mem with h_in_s' | h_unvis_s'
      · -- ⟨idx, h_lt⟩ ∈ s'.order = s.order ⇒ s.visited[⟨idx, h_lt⟩] = true (by h_visited).
        -- Definitionally = s.visited[idx]'h_lt = true, contradicts h_v.
        exact h_v (h_visited ⟨idx, h_lt⟩ h_in_s')
      · -- s'.visited[⟨idx, h_lt⟩] = false. But we set it to true.
        have h_set_true : s'.visited[(⟨idx, h_lt⟩ : Fin objCount)] = true := by
          show (s.visited.set idx true h_lt)[idx]'h_lt = true
          exact Vector.getElem_set_self h_lt
        rw [h_set_true] at h_unvis_s'; cases h_unvis_s'
    refine ⟨?_, ?_⟩
    · -- orderVisited on push: ∀ i ∈ (s''.order.push ⟨idx, h_lt⟩), visited[i] = true.
      intro i h_in
      rcases Array.mem_push.mp h_in with h_in_s'' | h_eq
      · exact h_s''_v i h_in_s''
      · -- i = ⟨idx, h_lt⟩. Need s''.visited[⟨idx, h_lt⟩] = true.
        -- By monotonicity from s' (where s'.visited[idx] = true) through foldl.
        subst h_eq
        have h_s'_idx_true : s'.visited[(⟨idx, h_lt⟩ : Fin objCount)] = true := by
          show (s.visited.set idx true h_lt)[idx]'h_lt = true
          exact Vector.getElem_set_self h_lt
        exact (foldl_dfs_mono_subset fuel deps children s').1 _ h_s'_idx_true
    · -- Nodup: s''.order has Nodup, and ⟨idx, h_lt⟩ wasn't in s''.order.
      show ((s''.order.push ⟨idx, h_lt⟩).toList.map (·.val)).Nodup
      rw [Array.toList_push, List.map_append]
      refine List.nodup_append.mpr ⟨h_s''_n, ?_, ?_⟩
      · simp
      · intro a h_a_in_s'' b h_b_in_idx
        simp at h_b_in_idx
        obtain ⟨b', h_b'_mem, h_b'_eq⟩ := List.mem_map.mp h_a_in_s''
        intro h_a_eq_b
        apply h_idx_not_in_s''
        have h_b'_val : b'.val = idx :=
          h_b'_eq.trans (h_a_eq_b.trans h_b_in_idx)
        rw [show (⟨idx, h_lt⟩ : Fin objCount) = b' from Fin.ext h_b'_val.symm]
        exact Array.mem_toList_iff.mp h_b'_mem

theorem Init.order_nodup (g : LoadGraph) :
    ((Init.order g).toList.map (·.val)).Nodup := by
  unfold order computeOrder
  by_cases h : g.objects.size = 0
  · simp [h]
  · rw [if_neg (by simp [h])]
    exact (dfs_preserves_inv _ _ 0 _ (DfsState.Inv.empty _)).2

-- ============================================================================
-- DEFERRED: topological-on-DAG and completeness.
--
-- Topological-on-DAG: for every edge `(a, b) ∈ g.deps`, if `(a, b)` is
-- not on a cycle then `b` precedes `a` in `Init.order g`. Needs a cycle
-- predicate (or SCC infrastructure) we don't have yet. The operational
-- proxy "main is last" is also provable from the new-visit branch's
-- push structure (~80 lines including a `dfs_back` lemma) but fights
-- the `split` tactic on `dfs`'s dependent dite — a smaller version of
-- the issue we resolved above with element-based `Inv`.
--
-- Completeness: every `i : Fin g.objects.size` appears in `Init.order g`.
-- Needs an inductive "DFS visits every reachable" lemma plus the
-- claim from `Discover.discover` that every `g.objects` index is
-- reachable from 0 via `g.deps`. The latter is a Discover-side proof
-- that doesn't exist yet.
-- ============================================================================

section Example
-- Three-object DAG: 0 (main) → {1, 2}; 1 → {2}; 2 → ∅.
-- DFS from 0 visits 1 first, descends to 2, emits 2 then 1, then
-- returns and emits 0. Result: deps before dependents, main last.
#guard (computeOrder #[#[1, 2], #[2], #[]] 3).map (·.val) = #[2, 1, 0]

-- Empty graph → empty order.
#guard (computeOrder #[] 0).map (·.val) = #[]

-- Linear chain 0 → 1 → 2 → 3: deeper objects emit first.
#guard (computeOrder #[#[1], #[2], #[3], #[]] 4).map (·.val) = #[3, 2, 1, 0]

-- Cycle 0 → 1 → 0: visited-flag breaks the back-edge mid-descent;
-- both still emit (gabi 08 leaves cycle order undefined — we just
-- terminate without re-recursing).
#guard (computeOrder #[#[1], #[0]] 2).map (·.val) = #[1, 0]

-- Diamond: 0 → {1, 2}; 1 → {3}; 2 → {3}; 3 → ∅.
-- 3 is shared by 1 and 2 — DFS emits it once on the first visit.
#guard (computeOrder #[#[1, 2], #[3], #[3], #[]] 4).map (·.val) = #[3, 1, 2, 0]
end Example

end LeanLoad.Plan.Init

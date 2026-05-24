/-
Recursive discovery over explicit dependency work items.

The construction carrier (`Discovered`, with its smart constructors
and characterisation theorems) lives in `Builder.lean`. This file adds
the state-evolution layer on top:

  · `ActiveStack` — object indices currently on the recursive call stack.
     Together with `Discovered.DoneOrActive`, it classifies every discovered
     object as either complete (`postOrder`) or active. Active dedup hits are
     rejected because gabi 08 leaves cyclic init ordering undefined.

  · `WorkResult` / `WorkListAcc` — return types that thread the
     state-evolution invariants (`sizeMono`, `pendingPreserved`,
     `newRowsComplete`, `postOrder*`, `doneOrActive`) through the mutual recursion.
     `WorkResult` is what one `discoverWork` returns; `WorkListAcc` is what
     `discoverWorkList` carries through a list of `WorkItem`s.

  · `discoverWork finder fuel discovered work` — one recursive discovery call.
     Resolves the explicit `WorkItem`, dedups against `discovered.nameIx`
     (catches both already-finished and in-progress-via-cycle:
     `pushObject` inserts into `nameIx` BEFORE recursing into children,
     so cycles dedup immediately against the in-progress ancestor's idx and
     are reported as policy failures).
     On miss, pushes the object and folds over its child work items,
     recording each child edge via `recordDep`.

Object finders are abstract — `ObjectFinder m` from `Discover.Provider`.
`Discover.Finalize` seeds the traversal from the main object and
promotes the final `Discovered` to `Result`.
-/

import LeanLoad.Discover.Builder
import LeanLoad.Discover.Provider

namespace LeanLoad.Discover

open LeanLoad

-- ============================================================================
-- WorkResult / WorkListAcc — return types of discoverWork/discoverWorkList.
--
-- · `WorkResult s0` — what `discoverWork s0 ...` returns. Beyond the new state,
--   the returned idx, and the obvious `sizeMono`/`idxLt`, it also
--   carries two pending-tracking proofs that downstream code uses to
--   chain `recordDep` preconditions and discharge `LoadGraph.closure`:
--     · `pendingPreserved` — for every `j < s0.objects.size`, `discoverWork`
--       didn't touch `pending[j]` (recordDep's `src` is always either
--       `≥ s0.objects.size` (newly pushed) or inside a child discovery frame).
--     · `newRowsComplete` — for every `j` that `discoverWork` newly pushed,
--       `pending[j] = 0` on return (the discoverWorkList over that object's
--       child work items zeroed it out).
--
-- · `WorkListAcc s0 newIdx remaining` — what `discoverWorkList` carries through
--   iterating one object's child work items. The `remaining : Nat` parameter
--   tracks `state.pending[newIdx]`: starts at the full list length,
--   ends at `0`. Plus matching analogs of the WorkResult invariants for
--   old (`j < s0.size, j ≠ newIdx`) and new (`j ≥ s0.size`) rows.
-- ============================================================================

structure WorkResult (active : Discovered.ActiveStack) (s0 : Discovered) where
  state : Discovered
  idx : Nat
  sizeMono : s0.objects.size ≤ state.objects.size
  idxLt : idx < state.objects.size
  /-- Every discovered object remains either complete or active after this call. -/
  doneOrActive : state.DoneOrActive active
  /-- The returned object is complete. Dedup hits against active ancestors are
      dependency cycles and are rejected rather than returned. -/
  idxDone : idx ∈ state.postOrder.toList
  /-- `pending[j]` unchanged for old indices. -/
  pendingPreserved : ∀ (j : Nat) (h_j : j < s0.objects.size),
    (state.pending[j]'(by
        rw [state.pendingSize]; exact Nat.lt_of_lt_of_le h_j sizeMono))
      = (s0.pending[j]'(by rw [s0.pendingSize]; exact h_j))
  /-- Dependency rows for old indices are unchanged. Recursive discovery only
      records edges for objects pushed by that recursive call. -/
  depsPreserved : ∀ (j : Nat) (h_j : j < s0.objects.size),
    (state.deps[j]'(by
        rw [state.depsSize]; exact Nat.lt_of_lt_of_le h_j sizeMono))
      = (s0.deps[j]'(by rw [s0.depsSize]; exact h_j))
  /-- All newly-pushed objects' rows are complete (pending = 0). -/
  newRowsComplete : ∀ (j : Nat) (_h_lo : s0.objects.size ≤ j)
      (h_hi : j < state.objects.size),
    (state.pending[j]'(by rw [state.pendingSize]; exact h_hi)) = 0
  /-- postOrder size delta matches objects size delta: every newly-pushed
      object was `markComplete`d before its discoverWork returned. -/
  postOrderGrew : state.postOrder.size
    = s0.postOrder.size + (state.objects.size - s0.objects.size)
  /-- Old postOrder entries are preserved. -/
  postOrderPreserved : ∀ (x : Nat), x ∈ s0.postOrder.toList →
    x ∈ state.postOrder.toList
  /-- Every newly-pushed object appears in postOrder. -/
  postOrderContainsNew : ∀ (j : Nat) (_h_lo : s0.objects.size ≤ j)
      (_h_hi : j < state.objects.size),
    j ∈ state.postOrder.toList
  /-- Every entry in postOrder is either an old entry or a new index in
      `[s0.size, state.size)`. The converse of `postOrderPreserved` +
      `postOrderContainsNew`. -/
  postOrderRange : ∀ (x : Nat), x ∈ state.postOrder.toList →
    x ∈ s0.postOrder.toList ∨ s0.objects.size ≤ x

structure WorkListAcc (active : Discovered.ActiveStack) (s0 : Discovered) (newIdx : Nat)
    (remaining : Nat) where
  state : Discovered
  sizeMono : s0.objects.size ≤ state.objects.size
  newIdxLt : newIdx < state.objects.size
  /-- Every discovered object is either complete or active while this list is processed. -/
  doneOrActive : state.DoneOrActive active
  /-- `state.pending[newIdx]` tracks the unprocessed tail of the
      `elf.needed.toList` we started iterating. -/
  pendingNewIdxEq : (state.pending[newIdx]'(by
      rw [state.pendingSize]; exact newIdxLt)) = remaining
  /-- Old indices (≠ newIdx) keep their pending unchanged. -/
  pendingOldPreserved : ∀ (j : Nat) (h_j : j < s0.objects.size)
      (_h_ne : j ≠ newIdx),
    (state.pending[j]'(by
        rw [state.pendingSize]; exact Nat.lt_of_lt_of_le h_j sizeMono))
      = (s0.pending[j]'(by rw [s0.pendingSize]; exact h_j))
  /-- Old dependency rows (except the parent row `newIdx`, which this fold is
      actively appending to) are unchanged. -/
  depsOldPreserved : ∀ (j : Nat) (h_j : j < s0.objects.size)
      (_h_ne : j ≠ newIdx),
    (state.deps[j]'(by
        rw [state.depsSize]; exact Nat.lt_of_lt_of_le h_j sizeMono))
      = (s0.deps[j]'(by rw [s0.depsSize]; exact h_j))
  /-- Newly-pushed rows (other than newIdx) are complete. The exclusion
      `j ≠ newIdx` is necessary because newIdx's row is governed by
      `pendingNewIdxEq` — partway through discoverWorkList it has size > 0. -/
  newRowsComplete : ∀ (j : Nat) (_h_lo : s0.objects.size ≤ j)
      (_h_ne : j ≠ newIdx) (h_hi : j < state.objects.size),
    (state.pending[j]'(by rw [state.pendingSize]; exact h_hi)) = 0
  /-- postOrder size delta matches objects size delta. (newIdx itself
      isn't markCompleted yet — the caller does that after discoverWorkList.) -/
  postOrderGrew : state.postOrder.size
    = s0.postOrder.size + (state.objects.size - s0.objects.size)
  /-- Old postOrder entries are preserved. -/
  postOrderPreserved : ∀ (x : Nat), x ∈ s0.postOrder.toList →
    x ∈ state.postOrder.toList
  /-- Every newly-pushed object (in [s0.size, state.size)) is in
      postOrder. This excludes newIdx because newIdx is at index
      s0.size - 1 < s0.size (it was pushed by the caller before
      constructing this WorkListAcc with `s0 = post-pushObject state`). -/
  postOrderContainsNew : ∀ (j : Nat) (_h_lo : s0.objects.size ≤ j)
      (_h_hi : j < state.objects.size),
    j ∈ state.postOrder.toList
  /-- Every entry in postOrder is either old or in the new range. -/
  postOrderRange : ∀ (x : Nat), x ∈ state.postOrder.toList →
    x ∈ s0.postOrder.toList ∨ s0.objects.size ≤ x
  /-- newIdx is NOT yet in postOrder — gets added by the caller's
      markComplete after discoverWorkList finishes. Needed as markComplete's
      Nodup precondition. -/
  newIdxNotInPostOrder : newIdx ∉ state.postOrder.toList
  /-- Every dependency already recorded in `newIdx`'s row is complete. This is
      the local edge-order fact consumed by `markComplete`. -/
  newIdxDepsDone : ∀ t, t ∈ state.deps[newIdx]'(by
      rw [state.depsSize]; exact newIdxLt) → t ∈ state.postOrder.toList

-- ============================================================================
-- discoverWork / discoverWorkList — one recursive call + its work-list helper.
--
-- Mutual structural recursion: `discoverWork` recurses to `discoverWorkList` with
-- the same `fuel` (and a list of `WorkItem`s); `discoverWorkList` recurses to itself
-- on the tail of the list, and to `discoverWork` on the head with the same
-- `fuel`. The well-founded measure is the lexicographic pair
-- `(fuel, listLength)`.
-- ============================================================================

mutual

/-- Find a work item's dependency, dedup, push-on-miss, recurse into child work items.
    Fuel-bounded; mutual with `discoverWorkList`. -/
def discoverWork {m : Type → Type} [Monad m] [MonadExceptOf String m]
    (finder : ObjectFinder m) (fuel : Nat)
    (active : Discovered.ActiveStack) (s0 : Discovered) (h_active : s0.DoneOrActive active)
    (work : WorkItem) :
    m (WorkResult active s0) := do
  match fuel with
  | 0 => throw "discover: fuel exhausted"
  | fuel + 1 =>
    match ← finder.findDependency work with
    | none => throw s!"discover: cannot find '{work.needed}' (runpath={work.runpath})"
    | some obj =>
      let canonical := obj.name
      let elf := obj.elf
      match h_lookup : s0.nameIx[canonical]? with
      | some idx =>
        -- Dedup hit: completed objects are shared; active hits are dependency
        -- cycles, whose init order is undefined by gabi 08, so Discover rejects
        -- them rather than constructing a cyclic LoadGraph.
        have h_idx : idx < s0.objects.size :=
          findLoadedIdx_lt ((s0.nameIxValid canonical).symm.trans h_lookup)
        if h_cycle : idx ∈ active then
          throw s!"discover: dependency cycle involving '{canonical}'"
        else
          have h_done : idx ∈ s0.postOrder.toList := by
            exact Or.resolve_right (h_active idx h_idx) h_cycle
          pure { state := s0, idx
                 sizeMono := Nat.le_refl _
                 idxLt := h_idx
                 doneOrActive := h_active
                 idxDone := h_done
                 pendingPreserved := by intro j h_j; rfl
                 depsPreserved := by intro j h_j; rfl
                 newRowsComplete := by
                   intro j h_lo h_hi
                   exact absurd (Nat.lt_of_lt_of_le h_hi h_lo) (Nat.lt_irrefl _)
                 postOrderGrew := by simp
                 postOrderPreserved := by intro x h_mem; exact h_mem
                 postOrderContainsNew := by
                   intro j h_lo h_hi
                   exact absurd (Nat.lt_of_lt_of_le h_hi h_lo) (Nat.lt_irrefl _)
                 postOrderRange := by intro x h_mem; left; exact h_mem }
      | none =>
        -- Miss: push obj at newIdx, then recurse into child work items,
        -- recording each child edge on return.
        let newIdx := s0.objects.size
        let s1 := Discovered.pushObject s0 obj h_lookup
        have h_s1_size : s1.objects.size = s0.objects.size + 1 :=
          Discovered.pushObject_size s0 obj h_lookup
        have h_newIdx_lt_s1 : newIdx < s1.objects.size := by
          show s0.objects.size < s1.objects.size
          rw [h_s1_size]; omega
        have h_mono_s1 : s0.objects.size ≤ s1.objects.size := by
          rw [h_s1_size]; omega
        let childWork := WorkItem.ofNeededArray elf.runpath elf.needed
        -- Initial WorkListAcc on s1: remaining = childWork.length =
        -- elf.needed.size = pending[newIdx] (by pushObject_pending_new).
        have h_pend_new : (s1.pending[newIdx]'(by
            rw [s1.pendingSize]; exact h_newIdx_lt_s1))
              = childWork.length := by
          rw [Discovered.pushObject_pending_new s0 obj h_lookup]
          simp [childWork, WorkItem.ofNeededArray, Array.length_toList, elf]
        -- s1's postOrder = s0's postOrder (pushObject doesn't touch it).
        -- newIdx = s0.size is not in s0.postOrder (by s0.postOrderBounds).
        have h_newIdx_not_in_s1 : newIdx ∉ s1.postOrder.toList := by
          show s0.objects.size ∉ s0.postOrder.toList
          intro h_mem
          have h_bound : s0.objects.size < s0.objects.size := by
            have := Array.mem_toList_iff.mp h_mem
            exact s0.postOrderBounds _ this
          exact Nat.lt_irrefl _ h_bound
        have h_done_active_s1 : s1.DoneOrActive (newIdx :: active) := by
          intro i h_i
          by_cases h_old : i < s0.objects.size
          · rcases h_active i h_old with h_done | h_act
            · left
              exact h_done
            · right
              exact List.mem_cons_of_mem _ h_act
          · have h_i_eq : i = newIdx := by
              show i = s0.objects.size
              have h_i_lt : i < (s0.objects.push obj).size := h_i
              rw [Array.size_push] at h_i_lt
              omega
            right
            simp [h_i_eq, newIdx]
        let init : WorkListAcc (newIdx :: active) s1 newIdx childWork.length :=
          { state := s1
            sizeMono := Nat.le_refl _
            newIdxLt := h_newIdx_lt_s1
            doneOrActive := h_done_active_s1
            pendingNewIdxEq := h_pend_new
            pendingOldPreserved := by
              intro j h_j _h_ne
              rfl
            depsOldPreserved := by
              intro j h_j _h_ne
              rfl
            newRowsComplete := by
              intro j h_lo _h_ne h_hi
              exact absurd (Nat.lt_of_lt_of_le h_hi h_lo) (Nat.lt_irrefl _)
            postOrderGrew := by simp
            postOrderPreserved := by intro x h_mem; exact h_mem
            postOrderContainsNew := by
              intro j h_lo h_hi
              exact absurd (Nat.lt_of_lt_of_le h_hi h_lo) (Nat.lt_irrefl _)
            postOrderRange := by intro x h_mem; left; exact h_mem
            newIdxNotInPostOrder := h_newIdx_not_in_s1
            newIdxDepsDone := by
              intro t h_t
              show t ∈ s0.postOrder.toList
              have h_get : (s1.deps[newIdx]'(by
                  rw [s1.depsSize]; exact h_newIdx_lt_s1)) = (#[] : Array Nat) := by
                show (s0.deps.push #[])[s0.objects.size]'_ = (#[] : Array Nat)
                rw [Array.getElem_push, dif_neg]
                rw [s0.depsSize]; exact Nat.lt_irrefl _
              rw [h_get] at h_t
              exact absurd h_t (by simp) }
        let final ← discoverWorkList finder fuel (newIdx :: active) s1 newIdx childWork init
        -- Append newIdx to postOrder via markComplete (using
        -- WorkListAcc's newIdxNotInPostOrder as the Nodup precondition).
        let s_final := Discovered.markComplete final.state newIdx final.newIdxLt
          final.newIdxNotInPostOrder final.newIdxDepsDone
        -- Wrap into a WorkResult on s0.
        have h_mono_final : s0.objects.size ≤ s_final.objects.size :=
          Nat.le_trans h_mono_s1 final.sizeMono
        have h_newIdx_lt_final : newIdx < s_final.objects.size :=
          Nat.lt_of_lt_of_le h_newIdx_lt_s1 final.sizeMono
        have h_done_active_final : s_final.DoneOrActive active := by
          intro i h_i
          have h_i_final : i < final.state.objects.size := by
            show i < final.state.objects.size
            exact h_i
          rcases final.doneOrActive i h_i_final with h_done | h_act
          · left
            show i ∈ (final.state.postOrder.push newIdx).toList
            rw [Array.toList_push, List.mem_append]
            left
            exact h_done
          · have h_act' : i = newIdx ∨ i ∈ active := by
              simpa using h_act
            rcases h_act' with h_eq | h_tail
            · subst h_eq
              left
              show newIdx ∈ (final.state.postOrder.push newIdx).toList
              rw [Array.toList_push, List.mem_append]
              right
              simp
            · right
              exact h_tail
        pure {
          state := s_final
          idx := newIdx
          sizeMono := h_mono_final
          idxLt := h_newIdx_lt_final
          doneOrActive := h_done_active_final
          idxDone := by
            show newIdx ∈ (final.state.postOrder.push newIdx).toList
            rw [Array.toList_push, List.mem_append]
            right
            simp
          pendingPreserved := by
            intro j h_j
            -- j < s0.size = newIdx, so j ≠ newIdx; also j < s1.size.
            have h_j_s1 : j < s1.objects.size := by rw [h_s1_size]; omega
            have h_ne : j ≠ newIdx := by
              show j ≠ s0.objects.size
              exact Nat.ne_of_lt h_j
            have h_step1 := final.pendingOldPreserved j h_j_s1 h_ne
            have h_step2 := Discovered.pushObject_pending_old s0 obj h_lookup j h_j
            exact h_step1.trans h_step2
          depsPreserved := by
            intro j h_j
            have h_j_s1 : j < s1.objects.size := by rw [h_s1_size]; omega
            have h_ne : j ≠ newIdx := by
              show j ≠ s0.objects.size
              exact Nat.ne_of_lt h_j
            have h_step1 := final.depsOldPreserved j h_j_s1 h_ne
            have h_step2 := Discovered.pushObject_deps_old s0 obj h_lookup j h_j
            exact h_step1.trans h_step2
          newRowsComplete := by
            intro j h_lo h_hi
            -- j ∈ [s0.size, final.size). Split: j = newIdx (= s0.size)
            -- or j ≥ s1.size.
            by_cases h_eq : j = s0.objects.size
            · subst h_eq
              -- Goal: s_final.pending[s0.size] = 0. markComplete doesn't
              -- touch pending, so s_final.pending = final.state.pending.
              -- By pendingNewIdxEq with remaining = 0:
              exact final.pendingNewIdxEq
            · -- j > s0.size, so j ≥ s1.size = s0.size + 1, hence j ≠ newIdx.
              have h_j_ge_s1 : s1.objects.size ≤ j := by
                rw [h_s1_size]
                have : s0.objects.size < j := Nat.lt_of_le_of_ne h_lo (Ne.symm h_eq)
                omega
              have h_ne_newIdx : j ≠ newIdx := by
                show j ≠ s0.objects.size
                exact h_eq
              exact final.newRowsComplete j h_j_ge_s1 h_ne_newIdx h_hi
          postOrderGrew := by
            -- s_final.postOrder = final.state.postOrder.push newIdx.
            -- |final.state.postOrder| = |s1.postOrder| + (final.state.size - s1.size)
            --                        = |s0.postOrder| + (final.state.size - s0.size - 1).
            -- So |s_final.postOrder| = |s0.postOrder| + (final.state.size - s0.size).
            show (final.state.postOrder.push newIdx).size
                  = s0.postOrder.size + (final.state.objects.size - s0.objects.size)
            rw [Array.size_push]
            have h_grew := final.postOrderGrew
            have h_s1_po : s1.postOrder = s0.postOrder := rfl
            have h_final_size_ge : final.state.objects.size ≥ s1.objects.size :=
              final.sizeMono
            rw [h_grew, h_s1_po, h_s1_size] at *
            omega
          postOrderPreserved := by
            intro x h_mem
            -- x ∈ s0.postOrder → x ∈ s_final.postOrder = final.state.postOrder.push newIdx.
            show x ∈ (final.state.postOrder.push newIdx).toList
            rw [Array.toList_push, List.mem_append]
            left
            exact final.postOrderPreserved x h_mem
          postOrderContainsNew := by
            intro j h_lo h_hi
            -- j ∈ [s0.size, s_final.size). Split: j = s0.size (= newIdx)
            -- or j > s0.size (so j ≥ s1.size).
            show j ∈ (final.state.postOrder.push newIdx).toList
            rw [Array.toList_push, List.mem_append]
            by_cases h_eq : j = s0.objects.size
            · right; simp [h_eq, newIdx]
            · left
              have h_j_ge_s1 : s1.objects.size ≤ j := by
                rw [h_s1_size]
                have : s0.objects.size < j := Nat.lt_of_le_of_ne h_lo (Ne.symm h_eq)
                omega
              exact final.postOrderContainsNew j h_j_ge_s1 h_hi
          postOrderRange := by
            intro x h_mem
            -- x ∈ s_final.postOrder = final.state.postOrder.push newIdx.
            -- Either x ∈ final.state.postOrder or x = newIdx.
            show x ∈ s0.postOrder.toList ∨ s0.objects.size ≤ x
            have h_mem' : x ∈ (final.state.postOrder.push newIdx).toList := h_mem
            rw [Array.toList_push, List.mem_append] at h_mem'
            rcases h_mem' with h_in_final | h_eq_newIdx
            · -- x ∈ final.state.postOrder. By final.postOrderRange (s1 base):
              -- x ∈ s1.postOrder OR s1.size ≤ x.
              -- s1.postOrder = s0.postOrder, s1.size = s0.size + 1.
              have h_range := final.postOrderRange x h_in_final
              show x ∈ s0.postOrder.toList ∨ s0.objects.size ≤ x
              rcases h_range with h_in_s1 | h_ge_s1
              · left
                show x ∈ s0.postOrder.toList
                -- s1.postOrder = s0.postOrder
                exact h_in_s1
              · right
                rw [h_s1_size] at h_ge_s1; omega
            · -- x = newIdx = s0.size. Second disjunct.
              right
              rw [List.mem_singleton] at h_eq_newIdx
              show s0.objects.size ≤ x
              omega }

/-- Process a list of dependency work items for an object at `newIdx`. For each
    item: recurse via `discoverWork`, then `recordDep newIdx childIdx` into the
    returned state. Threads `WorkListAcc` through the recursion. -/
def discoverWorkList {m : Type → Type} [Monad m] [MonadExceptOf String m]
    (finder : ObjectFinder m) (fuel : Nat)
    (active : Discovered.ActiveStack) (s0 : Discovered) (newIdx : Nat)
    (work : List WorkItem) (acc : WorkListAcc active s0 newIdx work.length) :
    m (WorkListAcc active s0 newIdx 0) := do
  match work, acc with
  | [], acc =>
    -- Base case: `[].length = 0` definitionally, so acc fits the return type.
    pure acc
  | next :: rest, acc =>
    -- `(next :: rest).length = rest.length + 1` definitionally, so acc' is a cast.
    let acc' : WorkListAcc active s0 newIdx (rest.length + 1) := acc
    let sub ← discoverWork finder fuel active acc'.state acc'.doneOrActive next
    -- recordDep preconditions:
    --   · h_src : newIdx < sub.state.objects.size (from acc.newIdxLt + sub.sizeMono).
    --   · h_tgt : sub.idx < sub.state.objects.size (= sub.idxLt).
    --   · h_pending : sub.state.pending[newIdx] > 0.
    --     By sub.pendingPreserved on j = newIdx (newIdx < acc'.state.size by acc'.newIdxLt):
    --       sub.state.pending[newIdx] = acc'.state.pending[newIdx] = rest.length + 1 > 0.
    have h_src : newIdx < sub.state.objects.size :=
      Nat.lt_of_lt_of_le acc'.newIdxLt sub.sizeMono
    have h_pend_pre_sub : (sub.state.pending[newIdx]'(by
        rw [sub.state.pendingSize]; exact h_src))
        = (acc'.state.pending[newIdx]'(by
            rw [acc'.state.pendingSize]; exact acc'.newIdxLt)) :=
      sub.pendingPreserved newIdx acc'.newIdxLt
    have h_pending_pos : (sub.state.pending[newIdx]'(by
        rw [sub.state.pendingSize]; exact h_src)) > 0 := by
      rw [h_pend_pre_sub, acc'.pendingNewIdxEq]
      omega
    have h_newIdx_not_in_sub : newIdx ∉ sub.state.postOrder.toList := by
      intro h_mem
      rcases sub.postOrderRange newIdx h_mem with h_in_acc | h_ge_acc
      · exact acc'.newIdxNotInPostOrder h_in_acc
      · exact Nat.not_lt.mpr h_ge_acc acc'.newIdxLt
    let s' := Discovered.recordDep sub.state newIdx sub.idx h_src sub.idxLt h_pending_pos
      h_newIdx_not_in_sub
    -- Build the new accumulator for the recursive call on `rest`.
    have h_mono' : s0.objects.size ≤ s'.objects.size := by
      show s0.objects.size ≤ sub.state.objects.size
      exact Nat.le_trans acc'.sizeMono sub.sizeMono
    have h_newIdx_lt' : newIdx < s'.objects.size := by
      show newIdx < sub.state.objects.size
      exact h_src
    have h_pendingNewIdxEq' : (s'.pending[newIdx]'(by
        rw [s'.pendingSize]; exact h_newIdx_lt'))
        = rest.length := by
      -- s' = Discovered.recordDep sub.state newIdx sub.idx _ _ _.
      -- recordDep with src=newIdx decrements pending[newIdx] by 1.
      show ((sub.state.pending.modify newIdx (· - 1))[newIdx]'_) = _
      rw [Array.getElem_modify _]
      simp
      rw [h_pend_pre_sub, acc'.pendingNewIdxEq]
      omega
    have h_pendingOldPreserved' : ∀ (j : Nat) (h_j : j < s0.objects.size)
        (h_ne : j ≠ newIdx),
        (s'.pending[j]'(by
            rw [s'.pendingSize]
            exact Nat.lt_of_lt_of_le h_j h_mono'))
          = (s0.pending[j]'(by rw [s0.pendingSize]; exact h_j)) := by
      intro j h_j h_ne
      -- Three steps:
      --   1. s'.pending[j] = sub.state.pending[j] (recordDep src≠j).
      --   2. sub.state.pending[j] = acc'.state.pending[j] (sub.pendingPreserved).
      --   3. acc'.state.pending[j] = s0.pending[j] (acc'.pendingOldPreserved).
      have h_step1 := Discovered.recordDep_pending_other sub.state
        newIdx sub.idx h_src sub.idxLt h_pending_pos h_newIdx_not_in_sub j
        (Nat.lt_of_lt_of_le h_j h_mono') (fun h_eq => h_ne h_eq.symm)
      have h_step2 := sub.pendingPreserved j
        (Nat.lt_of_lt_of_le h_j acc'.sizeMono)
      have h_step3 := acc'.pendingOldPreserved j h_j h_ne
      exact h_step1.trans (h_step2.trans h_step3)
    have h_depsOldPreserved' : ∀ (j : Nat) (h_j : j < s0.objects.size)
        (h_ne : j ≠ newIdx),
        (s'.deps[j]'(by
            rw [s'.depsSize]
            exact Nat.lt_of_lt_of_le h_j h_mono'))
          = (s0.deps[j]'(by rw [s0.depsSize]; exact h_j)) := by
      intro j h_j h_ne
      have h_step1 := Discovered.recordDep_deps_other sub.state
        newIdx sub.idx h_src sub.idxLt h_pending_pos h_newIdx_not_in_sub j
        (Nat.lt_of_lt_of_le h_j h_mono') (fun h_eq => h_ne h_eq.symm)
      have h_step2 := sub.depsPreserved j
        (Nat.lt_of_lt_of_le h_j acc'.sizeMono)
      have h_step3 := acc'.depsOldPreserved j h_j h_ne
      exact h_step1.trans (h_step2.trans h_step3)
    have h_newRowsComplete' : ∀ (j : Nat) (_h_lo : s0.objects.size ≤ j)
        (h_ne : j ≠ newIdx) (h_hi : j < s'.objects.size),
        (s'.pending[j]'(by rw [s'.pendingSize]; exact h_hi)) = 0 := by
      intro j h_lo h_ne h_hi
      -- j ≥ s0.size, j ≠ newIdx, j < s'.size = sub.state.size. Split on
      -- whether j was already in acc'.state's range or pushed by sub-discovery.
      have h_hi_sub : j < sub.state.objects.size := h_hi
      -- Step 1: s'.pending[j] = sub.state.pending[j] (recordDep src=newIdx,
      -- so other rows untouched).
      have h_step1 := Discovered.recordDep_pending_other sub.state
        newIdx sub.idx h_src sub.idxLt h_pending_pos h_newIdx_not_in_sub j h_hi_sub
        (fun h_eq => h_ne h_eq.symm)
      -- Step 2: cases on whether j was in acc'.state or pushed by sub-discovery.
      by_cases h_in_acc : j < acc'.state.objects.size
      · -- j < acc'.state.size: use acc'.newRowsComplete then sub.pendingPreserved.
        have h_step_acc := acc'.newRowsComplete j h_lo h_ne h_in_acc
        have h_step_sub := sub.pendingPreserved j h_in_acc
        -- sub.state.pending[j] = acc'.state.pending[j] = 0.
        rw [h_step1]
        exact h_step_sub.trans h_step_acc
      · -- j ≥ acc'.state.size: use sub.newRowsComplete.
        have h_in_acc' : acc'.state.objects.size ≤ j := Nat.le_of_not_lt h_in_acc
        have h_step_new := sub.newRowsComplete j h_in_acc' h_hi_sub
        rw [h_step1]
        exact h_step_new
    -- postOrder invariants for acc'' :
    have h_postOrderGrew' : s'.postOrder.size
        = s0.postOrder.size + (s'.objects.size - s0.objects.size) := by
      -- s'.postOrder = sub.state.postOrder (recordDep unchanged).
      -- Combine sub.postOrderGrew and acc'.postOrderGrew. omega needs
      -- sizeMono facts to handle the Nat subtractions.
      show sub.state.postOrder.size
            = s0.postOrder.size + (sub.state.objects.size - s0.objects.size)
      have h_sub := sub.postOrderGrew
      have h_acc := acc'.postOrderGrew
      have h_mono_sub := sub.sizeMono
      have h_mono_acc := acc'.sizeMono
      omega
    have h_postOrderPreserved' : ∀ (x : Nat), x ∈ s0.postOrder.toList →
        x ∈ s'.postOrder.toList := by
      intro x h_mem
      -- x ∈ s0.postOrder → (acc'.postOrderPreserved) → x ∈ acc'.state.postOrder
      --                   → (sub.postOrderPreserved) → x ∈ sub.state.postOrder = s'.postOrder.
      have h_acc := acc'.postOrderPreserved x h_mem
      have h_sub := sub.postOrderPreserved x h_acc
      show x ∈ sub.state.postOrder.toList
      exact h_sub
    have h_postOrderContainsNew' : ∀ (j : Nat), s0.objects.size ≤ j →
        j < s'.objects.size → j ∈ s'.postOrder.toList := by
      intro j h_lo h_hi
      -- j ∈ [s0.size, s'.size). s'.size = sub.state.size.
      -- Split on whether j < acc'.state.size or j ≥ acc'.state.size.
      have h_hi_sub : j < sub.state.objects.size := h_hi
      show j ∈ sub.state.postOrder.toList
      by_cases h_in_acc : j < acc'.state.objects.size
      · -- j was in acc'.state's range: use acc'.postOrderContainsNew, then sub.postOrderPreserved.
        have h_acc_new := acc'.postOrderContainsNew j h_lo h_in_acc
        exact sub.postOrderPreserved j h_acc_new
      · -- j ≥ acc'.state.size: use sub.postOrderContainsNew.
        have h_in_acc' : acc'.state.objects.size ≤ j := Nat.le_of_not_lt h_in_acc
        exact sub.postOrderContainsNew j h_in_acc' h_hi_sub
    have h_postOrderRange' : ∀ (x : Nat), x ∈ s'.postOrder.toList →
        x ∈ s0.postOrder.toList ∨ s0.objects.size ≤ x := by
      intro x h_mem
      show x ∈ s0.postOrder.toList ∨ s0.objects.size ≤ x
      -- x ∈ s'.postOrder = sub.state.postOrder.
      -- sub.postOrderRange: x ∈ acc'.state.postOrder OR acc'.state.size ≤ x.
      have h_mem_sub : x ∈ sub.state.postOrder.toList := h_mem
      have h_range_sub := sub.postOrderRange x h_mem_sub
      rcases h_range_sub with h_in_acc | h_ge_acc
      · -- x ∈ acc'.state.postOrder. By acc'.postOrderRange: in s0.postOrder OR ≥ s0.size.
        exact acc'.postOrderRange x h_in_acc
      · -- x ≥ acc'.state.size ≥ s0.size.
        right; exact Nat.le_trans acc'.sizeMono h_ge_acc
    have h_newIdxNotInPostOrder' : newIdx ∉ s'.postOrder.toList := by
      -- Suppose newIdx ∈ s'.postOrder.toList. By sub.postOrderRange:
      --   newIdx ∈ acc'.state.postOrder.toList OR acc'.state.size ≤ newIdx.
      -- Case 1: newIdx ∈ acc'.state.postOrder.toList — contradicts acc'.newIdxNotInPostOrder.
      -- Case 2: acc'.state.size ≤ newIdx — contradicts acc'.newIdxLt.
      exact h_newIdx_not_in_sub
    have h_newIdxDepsDone' : ∀ t, t ∈ s'.deps[newIdx]'(by
        rw [s'.depsSize]; exact h_newIdx_lt') → t ∈ s'.postOrder.toList := by
      intro t h_t
      show t ∈ sub.state.postOrder.toList
      have h_src_deps : newIdx < sub.state.deps.size := by
        rw [sub.state.depsSize]; exact h_src
      have h_get :
          s'.deps[newIdx]'(by rw [s'.depsSize]; exact h_newIdx_lt')
            = (sub.state.deps[newIdx]'h_src_deps).push sub.idx := by
        show (recordEdge sub.state.deps newIdx sub.idx)[newIdx]'_
            = (sub.state.deps[newIdx]'h_src_deps).push sub.idx
        unfold recordEdge
        rw [Array.getElem_modify]
        simp
      rw [h_get] at h_t
      rcases Array.mem_push.mp h_t with h_old | h_eq
      · have h_pres := sub.depsPreserved newIdx acc'.newIdxLt
        rw [h_pres] at h_old
        exact sub.postOrderPreserved t (acc'.newIdxDepsDone t h_old)
      · subst h_eq
        exact sub.idxDone
    have h_done_active' : s'.DoneOrActive active := by
      intro i h_i
      show i ∈ sub.state.postOrder.toList ∨ i ∈ active
      exact sub.doneOrActive i h_i
    let acc'' : WorkListAcc active s0 newIdx rest.length :=
      { state := s'
        sizeMono := h_mono'
        newIdxLt := h_newIdx_lt'
        doneOrActive := h_done_active'
        pendingNewIdxEq := h_pendingNewIdxEq'
        pendingOldPreserved := h_pendingOldPreserved'
        depsOldPreserved := h_depsOldPreserved'
        newRowsComplete := h_newRowsComplete'
        postOrderGrew := h_postOrderGrew'
        postOrderPreserved := h_postOrderPreserved'
        postOrderContainsNew := h_postOrderContainsNew'
        postOrderRange := h_postOrderRange'
        newIdxNotInPostOrder := h_newIdxNotInPostOrder'
        newIdxDepsDone := h_newIdxDepsDone' }
    discoverWorkList finder fuel active s0 newIdx rest acc''

end

end LeanLoad.Discover

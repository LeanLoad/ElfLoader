/-
Recursive discovery over explicit dependency work items.

The construction carrier (`Discovered`, with its smart constructors
and characterisation theorems) lives in `Discovered.lean`. This file adds
the state-evolution layer on top:

  · `WorkResult` / `WorkListAcc` — return types that thread the
     state-evolution invariants (`sizeMono`, `pendingPreserved`,
     `newRowsComplete`, `postOrder*`) through the mutual recursion.
     `WorkResult` is what one `discoverWork` returns; `WorkListAcc` is what
     `discoverWorkList` carries through a list of `WorkItem`s.

  · `discoverWork resolver fuel discovered work` — one recursive discovery call.
     Resolves the explicit `WorkItem`, dedups against `discovered.nameIx`
     (catches both already-finished and in-progress-via-cycle:
     `pushObject` inserts into `nameIx` BEFORE recursing into children,
     so cycles dedup immediately against the in-progress ancestor's idx).
     On miss, pushes the object and folds over its child work items,
     recording each child edge via `recordDep`.

Resolvers are abstract — `Resolver m` from `Discover/Resolver.lean`.
`Discover.Finalize` seeds the traversal from the main object and
promotes the final `Discovered` to `LoadGraph`.
-/

import LeanLoad.Discover.Discovered
import LeanLoad.Discover.Resolver

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

structure WorkResult (s0 : Discovered) where
  state : Discovered
  idx : Nat
  sizeMono : s0.objects.size ≤ state.objects.size
  idxLt : idx < state.objects.size
  /-- `pending[j]` unchanged for old indices. -/
  pendingPreserved : ∀ (j : Nat) (h_j : j < s0.objects.size),
    (state.pending[j]'(by
        rw [state.pendingSize]; exact Nat.lt_of_lt_of_le h_j sizeMono))
      = (s0.pending[j]'(by rw [s0.pendingSize]; exact h_j))
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

structure WorkListAcc (s0 : Discovered) (newIdx : Nat) (remaining : Nat) where
  state : Discovered
  sizeMono : s0.objects.size ≤ state.objects.size
  newIdxLt : newIdx < state.objects.size
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

/-- Resolve a work item, dedup, push-on-miss, recurse into child work items.
    Fuel-bounded; mutual with `discoverWorkList`. -/
def discoverWork {m : Type → Type} [Monad m] (resolver : Resolver m) (fuel : Nat)
    (s0 : Discovered) (work : WorkItem) :
    m (WorkResult s0) := do
  match fuel with
  | 0 => resolver.fail "discover: fuel exhausted"
  | fuel + 1 =>
    match ← resolver.resolve work with
    | none => resolver.fail s!"discover: cannot find '{work.needed}' (runpath={work.runpath})"
    | some resolved =>
      let canonical := resolved.name
      let handle := resolved.handle
      let elf := resolved.elf
      match h_lookup : s0.nameIx[canonical]? with
      | some idx =>
        -- Dedup hit: nothing changes, all invariants trivial.
        have h_idx : idx < s0.objects.size :=
          findLoadedIdx_lt ((s0.nameIxValid canonical).symm.trans h_lookup)
        pure { state := s0, idx
               sizeMono := Nat.le_refl _
               idxLt := h_idx
               pendingPreserved := by intro j h_j; rfl
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
        let obj : LoadedObject := { name := canonical, handle, elf }
        let newIdx := s0.objects.size
        let s1 := s0.pushObject obj h_lookup
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
          simp [obj, childWork, WorkItem.ofNeededArray, Array.length_toList]
        -- s1's postOrder = s0's postOrder (pushObject doesn't touch it).
        -- newIdx = s0.size is not in s0.postOrder (by s0.postOrderBounds).
        have h_newIdx_not_in_s1 : newIdx ∉ s1.postOrder.toList := by
          show s0.objects.size ∉ s0.postOrder.toList
          intro h_mem
          have h_bound : s0.objects.size < s0.objects.size := by
            have := Array.mem_toList_iff.mp h_mem
            exact s0.postOrderBounds _ this
          exact Nat.lt_irrefl _ h_bound
        let init : WorkListAcc s1 newIdx childWork.length :=
          { state := s1
            sizeMono := Nat.le_refl _
            newIdxLt := h_newIdx_lt_s1
            pendingNewIdxEq := h_pend_new
            pendingOldPreserved := by
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
            newIdxNotInPostOrder := h_newIdx_not_in_s1 }
        let final ← discoverWorkList resolver fuel s1 newIdx childWork init
        -- Append newIdx to postOrder via markComplete (using
        -- WorkListAcc's newIdxNotInPostOrder as the Nodup precondition).
        let s_final := final.state.markComplete newIdx final.newIdxLt
          final.newIdxNotInPostOrder
        -- Wrap into a WorkResult on s0.
        have h_mono_final : s0.objects.size ≤ s_final.objects.size :=
          Nat.le_trans h_mono_s1 final.sizeMono
        have h_newIdx_lt_final : newIdx < s_final.objects.size :=
          Nat.lt_of_lt_of_le h_newIdx_lt_s1 final.sizeMono
        pure {
          state := s_final
          idx := newIdx
          sizeMono := h_mono_final
          idxLt := h_newIdx_lt_final
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
def discoverWorkList {m : Type → Type} [Monad m] (resolver : Resolver m) (fuel : Nat)
    (s0 : Discovered) (newIdx : Nat)
    (work : List WorkItem) (acc : WorkListAcc s0 newIdx work.length) :
    m (WorkListAcc s0 newIdx 0) := do
  match work, acc with
  | [], acc =>
    -- Base case: `[].length = 0` definitionally, so acc fits the return type.
    pure acc
  | next :: rest, acc =>
    -- `(next :: rest).length = rest.length + 1` definitionally, so acc' is a cast.
    let acc' : WorkListAcc s0 newIdx (rest.length + 1) := acc
    let sub ← discoverWork resolver fuel acc'.state next
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
    let s' := sub.state.recordDep newIdx sub.idx h_src sub.idxLt h_pending_pos
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
      -- s' = sub.state.recordDep newIdx sub.idx _ _ _.
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
        newIdx sub.idx h_src sub.idxLt h_pending_pos j
        (Nat.lt_of_lt_of_le h_j h_mono') (fun h_eq => h_ne h_eq.symm)
      have h_step2 := sub.pendingPreserved j
        (Nat.lt_of_lt_of_le h_j acc'.sizeMono)
      have h_step3 := acc'.pendingOldPreserved j h_j h_ne
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
        newIdx sub.idx h_src sub.idxLt h_pending_pos j h_hi_sub
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
      show newIdx ∉ sub.state.postOrder.toList
      intro h_mem
      rcases sub.postOrderRange newIdx h_mem with h_in_acc | h_ge_acc
      · exact acc'.newIdxNotInPostOrder h_in_acc
      · exact Nat.not_lt.mpr h_ge_acc acc'.newIdxLt
    let acc'' : WorkListAcc s0 newIdx rest.length :=
      { state := s'
        sizeMono := h_mono'
        newIdxLt := h_newIdx_lt'
        pendingNewIdxEq := h_pendingNewIdxEq'
        pendingOldPreserved := h_pendingOldPreserved'
        newRowsComplete := h_newRowsComplete'
        postOrderGrew := h_postOrderGrew'
        postOrderPreserved := h_postOrderPreserved'
        postOrderContainsNew := h_postOrderContainsNew'
        postOrderRange := h_postOrderRange'
        newIdxNotInPostOrder := h_newIdxNotInPostOrder' }
    discoverWorkList resolver fuel s0 newIdx rest acc''

end

end LeanLoad.Discover

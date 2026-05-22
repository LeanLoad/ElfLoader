/-
DFS driver — the recursive traversal that walks `DT_NEEDED` edges
from main and assembles a `LoadGraph`.

The construction carrier (`DfsState`, with its smart constructors
and characterisation theorems) lives in `State.lean`. This file
adds three layers on top:

  · `DfsResult` / `NeededAcc` — return types that thread the
     state-evolution invariants (`sizeMono`, `pendingPreserved`,
     `newRowsComplete`, `postOrder*`) through the mutual recursion.
     `DfsResult` is what one `dfs` returns; `NeededAcc` is what
     `dfsList` carries through `elf.needed.toList`.

  · `dfs eff fuel s soname runpath` — one recursive DFS call.
     Resolves `soname` via `eff.resolveDep`, dedups against
     `s.nameIx` (catches both already-finished and in-progress-
     via-cycle: `pushObject` inserts into `nameIx` BEFORE recursing
     into children, so cycles dedup immediately against the
     in-progress ancestor's idx). On miss, pushes the obj and
     folds over `elf.needed` recursively recording each child
     edge via `recordDep`.

  · `discoverWith eff fuel mainObj` — drive the DFS over main's
     NEEDED list, then promote the final `DfsState` to a
     `LoadGraph` by proving `closure` pointwise from `rowSum`
     + `pending = 0` everywhere.

Effects are abstract — `Effects m` from `Discover/Effects.lean`.
Production wires `Effects.io` over `IO` in `Discover/IO.lean`; tests
wire `Effects.test` over `Except String` in `Discover/Test.lean`.
-/

import LeanLoad.Discover.State
import LeanLoad.Discover.Effects

namespace LeanLoad.Discover

open LeanLoad

-- ============================================================================
-- DfsResult / NeededAcc — the return types of `dfs` and `dfsList`.
--
-- · `DfsResult s0` — what `dfs s0 ...` returns. Beyond the new state,
--   the returned idx, and the obvious `sizeMono`/`idxLt`, it also
--   carries two pending-tracking proofs that downstream code uses to
--   chain `recordDep` preconditions and discharge `LoadGraph.closure`:
--     · `pendingPreserved` — for every `j < s0.objects.size`, `dfs`
--       didn't touch `pending[j]` (recordDep's `src` is always either
--       `≥ s0.objects.size` (newly pushed) or in a sub-dfs's frame).
--     · `newRowsComplete` — for every `j` that `dfs` newly pushed,
--       `pending[j] = 0` on return (the dfsList over that obj's
--       `elf.needed.toList` zeroed it out).
--
-- · `NeededAcc s0 newIdx remaining` — what `dfsList` carries through
--   iterating `elf.needed.toList`. The `remaining : Nat` parameter
--   tracks `state.pending[newIdx]`: starts at the full list length,
--   ends at `0`. Plus matching analogs of the DfsResult invariants for
--   old (`j < s0.size, j ≠ newIdx`) and new (`j ≥ s0.size`) rows.
-- ============================================================================

structure DfsResult (s0 : DfsState) where
  state : DfsState
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
      object was `markComplete`d before its dfs returned. -/
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

structure NeededAcc (s0 : DfsState) (newIdx : Nat) (remaining : Nat) where
  state : DfsState
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
      `pendingNewIdxEq` — partway through dfsList it has size > 0. -/
  newRowsComplete : ∀ (j : Nat) (_h_lo : s0.objects.size ≤ j)
      (_h_ne : j ≠ newIdx) (h_hi : j < state.objects.size),
    (state.pending[j]'(by rw [state.pendingSize]; exact h_hi)) = 0
  /-- postOrder size delta matches objects size delta. (newIdx itself
      isn't markCompleted yet — the caller does that after dfsList.) -/
  postOrderGrew : state.postOrder.size
    = s0.postOrder.size + (state.objects.size - s0.objects.size)
  /-- Old postOrder entries are preserved. -/
  postOrderPreserved : ∀ (x : Nat), x ∈ s0.postOrder.toList →
    x ∈ state.postOrder.toList
  /-- Every newly-pushed object (in [s0.size, state.size)) is in
      postOrder. This excludes newIdx because newIdx is at index
      s0.size - 1 < s0.size (it was pushed by the caller before
      constructing this NeededAcc with `s0 = post-pushObject state`). -/
  postOrderContainsNew : ∀ (j : Nat) (_h_lo : s0.objects.size ≤ j)
      (_h_hi : j < state.objects.size),
    j ∈ state.postOrder.toList
  /-- Every entry in postOrder is either old or in the new range. -/
  postOrderRange : ∀ (x : Nat), x ∈ state.postOrder.toList →
    x ∈ s0.postOrder.toList ∨ s0.objects.size ≤ x
  /-- newIdx is NOT yet in postOrder — gets added by the caller's
      markComplete after dfsList finishes. Needed as markComplete's
      Nodup precondition. -/
  newIdxNotInPostOrder : newIdx ∉ state.postOrder.toList

-- ============================================================================
-- dfs / dfsList — one recursive DFS call + its list-of-NEEDED helper.
--
-- Mutual structural recursion: `dfs` recurses to `dfsList` with the same
-- `fuel` (and a list of NEEDED strings); `dfsList` recurses to itself
-- on the tail of the list, and to `dfs` on the head with the same
-- `fuel`. The well-founded measure is the lexicographic pair
-- `(fuel, listLength)`.
-- ============================================================================

mutual

/-- Resolve `soname`, dedup, push-on-miss, recurse into elf.needed.
    Fuel-bounded; mutual with `dfsList`. -/
def dfs {m : Type → Type} [Monad m] (eff : Effects m) (fuel : Nat)
    (s0 : DfsState) (soname : String) (runpath : Option String) :
    m (DfsResult s0) := do
  match fuel with
  | 0 => eff.fail "discover: fuel exhausted"
  | fuel + 1 =>
    match ← eff.resolveDep soname runpath with
    | none => eff.fail s!"discover: cannot find '{soname}' (runpath={runpath})"
    | some (canonical, handle, elf) =>
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
        -- Miss: push obj at newIdx, then recurse into elf.needed via
        -- dfsList, recording each child edge on return.
        let obj : LoadedObject := { name := canonical, handle, elf }
        let newIdx := s0.objects.size
        let s1 := s0.pushObject obj h_lookup
        have h_s1_size : s1.objects.size = s0.objects.size + 1 :=
          DfsState.pushObject_size s0 obj h_lookup
        have h_newIdx_lt_s1 : newIdx < s1.objects.size := by
          show s0.objects.size < s1.objects.size
          rw [h_s1_size]; omega
        have h_mono_s1 : s0.objects.size ≤ s1.objects.size := by
          rw [h_s1_size]; omega
        -- Initial NeededAcc on s1: remaining = elf.needed.toList.length =
        -- elf.needed.size = pending[newIdx] (by pushObject_pending_new).
        have h_pend_new : (s1.pending[newIdx]'(by
            rw [s1.pendingSize]; exact h_newIdx_lt_s1))
              = elf.needed.toList.length := by
          rw [DfsState.pushObject_pending_new s0 obj h_lookup, Array.length_toList]
        -- s1's postOrder = s0's postOrder (pushObject doesn't touch it).
        -- newIdx = s0.size is not in s0.postOrder (by s0.postOrderBounds).
        have h_newIdx_not_in_s1 : newIdx ∉ s1.postOrder.toList := by
          show s0.objects.size ∉ s0.postOrder.toList
          intro h_mem
          have h_bound : s0.objects.size < s0.objects.size := by
            have := Array.mem_toList_iff.mp h_mem
            exact s0.postOrderBounds _ this
          exact Nat.lt_irrefl _ h_bound
        let init : NeededAcc s1 newIdx elf.needed.toList.length :=
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
        let final ← dfsList eff fuel s1 newIdx elf.runpath elf.needed.toList init
        -- Append newIdx to postOrder via markComplete (using
        -- NeededAcc's newIdxNotInPostOrder as the Nodup precondition).
        let s_final := final.state.markComplete newIdx final.newIdxLt
          final.newIdxNotInPostOrder
        -- Wrap into a DfsResult on s0.
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
            have h_step2 := DfsState.pushObject_pending_old s0 obj h_lookup j h_j
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

/-- Process a list of NEEDED strings for an object at `newIdx`. For each
    string: recurse via `dfs`, then `recordDep newIdx childIdx` into the
    returned state. Threads `NeededAcc` through the recursion. -/
def dfsList {m : Type → Type} [Monad m] (eff : Effects m) (fuel : Nat)
    (s0 : DfsState) (newIdx : Nat) (runpath : Option String)
    (needed : List String) (acc : NeededAcc s0 newIdx needed.length) :
    m (NeededAcc s0 newIdx 0) := do
  match needed, acc with
  | [], acc =>
    -- Base case: `[].length = 0` definitionally, so acc fits the return type.
    pure acc
  | n :: rest, acc =>
    -- `(n :: rest).length = rest.length + 1` definitionally, so acc' is a cast.
    let acc' : NeededAcc s0 newIdx (rest.length + 1) := acc
    let sub ← dfs eff fuel acc'.state n runpath
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
      have h_step1 := DfsState.recordDep_pending_other sub.state
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
      -- whether j was already in acc'.state's range or pushed by sub-dfs.
      have h_hi_sub : j < sub.state.objects.size := h_hi
      -- Step 1: s'.pending[j] = sub.state.pending[j] (recordDep src=newIdx,
      -- so other rows untouched).
      have h_step1 := DfsState.recordDep_pending_other sub.state
        newIdx sub.idx h_src sub.idxLt h_pending_pos j h_hi_sub
        (fun h_eq => h_ne h_eq.symm)
      -- Step 2: cases on whether j was in acc'.state or pushed by sub-dfs.
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
    let acc'' : NeededAcc s0 newIdx rest.length :=
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
    dfsList eff fuel s0 newIdx runpath rest acc''

end

-- ============================================================================
-- discoverWith — top-level driver. Seed with main, recurse into main's
-- NEEDED list via `dfsList` with `newIdx = 0` (each iteration records
-- an edge 0 → childIdx into main's row), then promote the final
-- `DfsState` to a `LoadGraph` by discharging the closure invariant
-- pointwise from `rowSum` + `pending = 0` everywhere.
-- ============================================================================

/-- Drive the DFS to completion against `eff`, then construct the
    `LoadGraph` output. The fuel cap is a Lean-termination concession
    (each new push strictly grows `objects.size`, so a true upper bound
    is "the total number of transitively-needed sonames"). -/
def discoverWith {m : Type → Type} [Monad m] (eff : Effects m) (fuel : Nat)
    (mainObj : LoadedObject) : m LoadGraph := do
  let s0 := DfsState.initial mainObj
  -- Drive DFS over main's NEEDED via `dfsList` with `newIdx = 0`. Each
  -- iteration: dfs(needed) → (sub, childIdx), then recordDep 0 childIdx.
  -- Initial NeededAcc: pending[0] = mainObj.elf.needed.size = toList.length.
  have h_pend_main : (s0.pending[0]'(by rw [s0.pendingSize]; exact s0.sizePos))
                      = mainObj.elf.needed.toList.length := by
    show ((#[mainObj.elf.needed.size] : Array Nat)[0]) = _
    simp [Array.length_toList]
  -- 0 ∉ s0.postOrder (s0.postOrder = #[], empty).
  have h_zero_not_in : (0 : Nat) ∉ s0.postOrder.toList := by
    show (0 : Nat) ∉ (#[] : Array Nat).toList
    simp
  let init : NeededAcc s0 0 mainObj.elf.needed.toList.length :=
    { state := s0
      sizeMono := Nat.le_refl _
      newIdxLt := s0.sizePos
      pendingNewIdxEq := h_pend_main
      pendingOldPreserved := by intro j h_j _h_ne; rfl
      newRowsComplete := by
        intro j h_lo _h_ne h_hi
        exact absurd (Nat.lt_of_lt_of_le h_hi h_lo) (Nat.lt_irrefl _)
      postOrderGrew := by simp
      postOrderPreserved := by intro x h_mem; exact h_mem
      postOrderContainsNew := by
        intro j h_lo h_hi
        exact absurd (Nat.lt_of_lt_of_le h_hi h_lo) (Nat.lt_irrefl _)
      postOrderRange := by intro x h_mem; left; exact h_mem
      newIdxNotInPostOrder := h_zero_not_in }
  let final ← dfsList eff fuel s0 0 mainObj.elf.runpath
    mainObj.elf.needed.toList init
  -- After dfsList, append main's idx (0) to postOrder via markComplete.
  -- markComplete needs 0 ∉ final.state.postOrder.toList, which is
  -- final.newIdxNotInPostOrder.
  let s_final := final.state.markComplete 0 final.newIdxLt
    final.newIdxNotInPostOrder
  -- Promote to LoadGraph by discharging closure + initOrder invariants.
  -- s_final.postOrder has size = s0.postOrder.size + (s_final.size - s0.size).
  -- s0.postOrder.size = 0, s_final.size = final.state.size = objects.size.
  -- So s_final.postOrder.size = objects.size.
  -- markComplete added 0; final's postOrderGrew said
  --   final.state.postOrder.size = s0.postOrder.size + (final.state.size - s0.size)
  --                              = 0 + (final.state.size - 1) = final.state.size - 1.
  -- After markComplete: s_final.postOrder.size = final.state.size = s_final.size.
  have h_initSize : s_final.postOrder.size = s_final.objects.size := by
    show (final.state.postOrder.push 0).size = final.state.objects.size
    rw [Array.size_push, final.postOrderGrew]
    have : s0.postOrder.size = 0 := by show #[].size = 0; rfl
    rw [this]
    have h_mono := final.sizeMono
    have h_s0_size : s0.objects.size = 1 := by show (#[mainObj] : Array LoadedObject).size = 1; rfl
    omega
  have h_initBounds : ∀ x ∈ s_final.postOrder, x < s_final.objects.size :=
    s_final.postOrderBounds
  -- Map each Nat in postOrder to Fin objects.size using the bounds.
  let initOrderArr : Array (Fin s_final.objects.size) :=
    s_final.postOrder.attach.map (fun p : {x // x ∈ s_final.postOrder} =>
      ⟨p.val, h_initBounds p.val p.property⟩)
  have h_initOrderArr_size : initOrderArr.size = s_final.objects.size := by
    show (s_final.postOrder.attach.map _).size = _
    rw [Array.size_map, Array.size_attach]
    exact h_initSize
  pure {
    objects := s_final.objects
    deps := s_final.deps
    initOrder := initOrderArr
    sizePos := s_final.sizePos
    namesNodup := s_final.namesNodup
    depsSize := s_final.depsSize
    depsBounds := s_final.depsBounds
    closure := by
      intro i h
      -- closure says deps[i].size = needed_i.size. By rowSum,
      -- deps[i].size + pending[i] = needed_i.size. So suffices to show
      -- pending[i] = 0. markComplete doesn't touch pending.
      have h_row := s_final.rowSum i h
      suffices h_pend : (s_final.pending[i]'(by
                          rw [s_final.pendingSize]; exact h)) = 0 by
        omega
      -- s_final.pending = final.state.pending (markComplete preserves).
      show (final.state.pending[i]'(by
              rw [final.state.pendingSize]; exact h)) = 0
      by_cases h_eq : i = 0
      · subst h_eq; exact final.pendingNewIdxEq
      · have h_lo : s0.objects.size ≤ i := by show 1 ≤ i; omega
        exact final.newRowsComplete i h_lo h_eq h
    initOrderSize := h_initOrderArr_size
    initOrderNodup := by
      -- s_final.postOrderNodup says s_final.postOrder.toList.Nodup.
      -- attach.map followed by `.val` recovers the original list, so Nodup transfers.
      show ((s_final.postOrder.attach.map (fun p : {x // x ∈ s_final.postOrder} =>
                (⟨p.val, h_initBounds p.val p.property⟩ : Fin s_final.objects.size))
            ).toList.map (·.val)).Nodup
      simp [Array.toList_map, Array.toList_attach]
      exact s_final.postOrderNodup
  }

end LeanLoad.Discover

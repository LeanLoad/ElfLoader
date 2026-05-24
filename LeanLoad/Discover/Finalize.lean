/-
Discover finalization — seed DFS from main and build `LoadGraph`.

`Traversal.lean` owns the mutual DFS over explicit `WorkItem`s and
threads state-evolution invariants through recursive discovery. This file
consumes that final `WorkListAcc`, marks the main object complete, and
promotes the final `Discovered` to the public `LoadGraph` by proving:

  · `closure` — every `deps[i]` row has one edge per `DT_NEEDED`.
  · `initOrderSize` — the DFS post-order covers every object.
  · `initOrderNodup` — post-order contains no duplicate indices.
-/

import LeanLoad.Discover.Traversal

namespace LeanLoad.Discover

open LeanLoad

-- ============================================================================
-- discoverWith — top-level finalizer. Seed with main, recurse into main's
-- work-item list via `discoverWorkList` with `newIdx = 0` (each iteration records
-- an edge 0 → childIdx into main's row), then promote the final
-- `Discovered` to a `LoadGraph` by discharging the closure invariant
-- pointwise from `rowSum` + `pending = 0` everywhere.
-- ============================================================================

/-- Drive the DFS to completion against `resolver`, then construct the
    `LoadGraph` output. The fuel cap is a Lean-termination concession
    (each new push strictly grows `objects.size`, so a true upper bound
    is "the total number of transitively-needed sonames"). -/
def discoverWith {m : Type → Type} [Monad m] (resolver : Resolver m) (fuel : Nat)
    (mainObj : LoadedObject) : m LoadGraph := do
  let s0 := Discovered.initial mainObj
  let initialWork := WorkItem.ofNeededArray mainObj.elf.runpath mainObj.elf.needed
  -- Drive DFS over main's NEEDED via `discoverWorkList` with `newIdx = 0`. Each
  -- iteration: discoverWork(work) → (sub, childIdx), then recordDep 0 childIdx.
  -- Initial WorkListAcc: pending[0] = mainObj.elf.needed.size = initialWork.length.
  have h_pend_main : (s0.pending[0]'(by rw [s0.pendingSize]; exact s0.sizePos))
                      = initialWork.length := by
    have h_length : initialWork.length = mainObj.elf.needed.size := by
      simp [initialWork, WorkItem.ofNeededArray, Array.length_toList]
    show ((#[mainObj.elf.needed.size] : Array Nat)[0]) = initialWork.length
    rw [h_length]
    simp
  -- 0 ∉ s0.postOrder (s0.postOrder = #[], empty).
  have h_zero_not_in : (0 : Nat) ∉ s0.postOrder.toList := by
    show (0 : Nat) ∉ (#[] : Array Nat).toList
    simp
  let init : WorkListAcc s0 0 initialWork.length :=
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
  let final ← discoverWorkList resolver fuel s0 0 initialWork init
  -- After discoverWorkList, append main's idx (0) to postOrder via markComplete.
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
    have h_s0_size : s0.objects.size = 1 := by
      show (#[mainObj] : Array LoadedObject).size = 1
      rfl
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

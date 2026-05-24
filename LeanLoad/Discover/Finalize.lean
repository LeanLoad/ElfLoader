/-
Discover finalization — seed DFS from main and build the public result.

`Traversal.lean` owns the mutual DFS over explicit `WorkItem`s and
threads state-evolution invariants through recursive discovery. This file
consumes that final `WorkListAcc`, marks the main object complete, and
promotes the final `Discovered` to a public `LoadGraph` plus graph-indexed
`InitOrder` by proving:

  · `closure` — every `deps[i]` row has one edge per `DT_NEEDED`.
  · `InitOrder.size` — the DFS post-order covers every object.
  · `InitOrder.nodup` — post-order contains no duplicate indices.
  · `InitOrder.classifiesDeps` — every graph edge is placed by the total
    schedule, with reverse/self placements representing deterministic cycle
    breaks because gabi 08 leaves cyclic init ordering unspecified.
-/

import LeanLoad.Discover.Traversal

namespace LeanLoad.Discover

open LeanLoad

-- ============================================================================
-- discoverFrom / discover — monadic top-level finalizers. Seed with main, recurse into main's
-- work-item list via `discoverWorkList` with `newIdx = 0` (each iteration records
-- an edge 0 → childIdx into main's row), then promote the final
-- `Discovered` to a `Result` by discharging the closure invariant
-- pointwise from `rowSum` + `pending = 0` everywhere.
-- ============================================================================

/-- Drive the DFS to completion against `finder`, starting from an already-discovered
    main object, then construct the public `Result`. The fuel cap is a Lean-termination concession
    (each new push strictly grows `objects.size`, so a true upper bound
    is "the total number of transitively-needed sonames"). -/
private def discoverFrom {m : Type → Type} [Monad m] [MonadExceptOf String m]
    (finder : ObjectFinder m) (fuel : Nat)
    (mainObj : DiscoveredObject) : m Result := do
  let s0 := Discovered.initial mainObj
  let initialWork :=
    WorkItem.ofNeededArray mainObj.originDir mainObj.elf.rpath mainObj.elf.runpath
      mainObj.elf.needed
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
  have h_done_active_s0 : s0.DoneOrActive [0] := by
    intro i h_i
    have h_i_zero : i = 0 := by
      have h_lt : i < (#[mainObj] : Array DiscoveredObject).size := h_i
      simp at h_lt
      omega
    right
    simp [h_i_zero]
  let init : WorkListAcc [0] s0 0 initialWork.length :=
    { state := s0
      sizeMono := Nat.le_refl _
      newIdxLt := s0.sizePos
      doneOrActive := h_done_active_s0
      pendingNewIdxEq := h_pend_main
      pendingOldPreserved := by intro j h_j _h_ne; rfl
      depsOldPreserved := by intro j h_j _h_ne; rfl
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
  let final ← discoverWorkList finder fuel [0] s0 0 initialWork init
  -- After discoverWorkList, append main's idx (0) to postOrder via markComplete.
  -- markComplete needs 0 ∉ final.state.postOrder.toList, which is
  -- final.newIdxNotInPostOrder.
  let s_final := Discovered.markComplete final.state 0 final.newIdxLt
    final.newIdxNotInPostOrder
  -- Promote to `Result` by discharging graph closure + init-order invariants.
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
      show (#[mainObj] : Array DiscoveredObject).size = 1
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
  have h_initOrderVals : initOrderArr.map (fun ix => ix.val) = s_final.postOrder := by
    simp [initOrderArr, Array.map_map, Function.comp_def]
  have h_allDone : ∀ i, i < s_final.objects.size → i ∈ s_final.postOrder.toList := by
    intro i h_i
    show i ∈ (final.state.postOrder.push 0).toList
    have h_i_final : i < final.state.objects.size := h_i
    rcases final.doneOrActive i h_i_final with h_done | h_active
    · rw [Array.toList_push, List.mem_append]
      left
      exact h_done
    · have h_i_zero : i = 0 := by
        simpa using h_active
      subst h_i_zero
      rw [Array.toList_push, List.mem_append]
      right
      simp
  let graph : LoadGraph := {
    objects := s_final.objects
    deps := s_final.deps
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
  }
  let initOrder : InitOrder graph := {
    order := initOrderArr
    size := h_initOrderArr_size
    covers := by
      intro i h_i
      rw [h_initOrderVals]
      exact h_allDone i h_i
    nodup := by
      -- s_final.postOrderNodup says s_final.postOrder.toList.Nodup.
      -- attach.map followed by `.val` recovers the original list, so Nodup transfers.
      show ((s_final.postOrder.attach.map (fun p : {x // x ∈ s_final.postOrder} =>
                (⟨p.val, h_initBounds p.val p.property⟩ : Fin s_final.objects.size))
            ).toList.map (·.val)).Nodup
      simp [Array.toList_map, Array.toList_attach]
      exact s_final.postOrderNodup
    classifiesDeps := by
      intro i j h_edge
      change j = i ∨
        LoadGraph.PostBefore (initOrderArr.map (fun ix => ix.val)) j i ∨
        LoadGraph.PostBefore (initOrderArr.map (fun ix => ix.val)) i j
      rw [h_initOrderVals]
      rcases h_edge with ⟨h_i, h_j⟩
      have h_i_obj : i < s_final.objects.size := by
        rw [← s_final.depsSize]
        exact h_i
      have h_j_obj : j < s_final.objects.size :=
        s_final.depsBounds i h_i j h_j
      exact LoadGraph.PostBefore.eq_or_before_or_after
        (h_allDone j h_j_obj) (h_allDone i h_i_obj)
  }
  pure { graph := graph, initOrder := initOrder }

/-- Fully monadic Discover entry point. The finder owns both the effectful
    `mainPath → DiscoveredObject` step and dependency lookup; traversal/finalization
    are shared by production IO and pure examples. -/
def discover {m : Type → Type} [Monad m] [MonadExceptOf String m]
    (finder : ObjectFinder m) (fuel : Nat)
    (mainPath : String) : m Result := do
  let mainObj ← finder.findMain mainPath
  discoverFrom finder fuel mainObj

end LeanLoad.Discover

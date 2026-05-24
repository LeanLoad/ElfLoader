/-
State-set construction carrier.

`State` holds everything resolved so far (objects + deps + a
name→idx HashMap accelerator) plus the invariants we maintain as
we traverse pending `WorkItem`s. Its field naming intentionally mirrors
`LoadGraph` so the final promotion (`Build.discoverWith`'s `LoadGraph`
mk) is mostly structural.

Carries the first four `LoadGraph` invariants plus `nameIxValid`
(the HashMap accelerator's bridge to the spec-level `findLoadedIdx`)
plus the `rowSum` / `postOrder*` invariants that `DFS` consumes.
The fifth `LoadGraph` invariant — `closure` — is *not* carried
here; individual push/recordDep steps break it. `closure` is
established at the very end of `Build.discoverWith`, when every
object's `deps` row has been fully populated.

Four smart constructors maintain the invariants:

  · `initial`       — seeds with main (idx 0).
  · `pushObject`    — adds a freshly-resolved object, empty deps row.
  · `recordDep`     — records one `src → tgt` edge.
  · `markComplete`  — appends `idx` to `postOrder` (DFS-return time).

Plus characterisation theorems (`*_size`, `*_postOrder`, `*_pending_*`)
used by `DFS.discoverWork` / `discoverWorkList` to discharge the
`WorkResult` / `WorkListAcc` invariants they thread through the recursion.
-/

import Std.Data.HashMap
import LeanLoad.Discover.Graph

namespace LeanLoad.Discover

open LeanLoad

-- ============================================================================
-- State — all loaded objects and partially recorded dependency edges.
-- ============================================================================

/-- State-set state. Field naming intentionally mirrors `LoadGraph`
    so the final promotion (`discoverWith`'s `LoadGraph` mk) is mostly
    structural — only `closure` is new (and falls out of `rowSum` once
    every `pending[i]` is `0`). -/
structure State where
  /-- Loaded objects discovered so far, in DFS pre-order. -/
  objects     : Array LoadedObject
  /-- Per-object dep edges. May be partial during DFS: row `i` is fully
      populated only after the discoverWork call that pushed `objects[i]` has
      returned. -/
  deps        : Array (Array Nat)
  /-- Name→idx dedup accelerator. Bridges to `findLoadedIdx` via
      `nameIxValid`. -/
  nameIx      : Std.HashMap String Nat
  /-- Per-object count of `DT_NEEDED` entries still to be recorded into
      `deps[i]`. Starts at `obj.elf.needed.size` when an object is
      pushed; decremented by `recordDep`. Tied to `deps[i].size` by
      `rowSum`. When `pending[i] = 0`, the row is complete — which is
      how `discoverWith` discharges `LoadGraph.closure`. -/
  pending     : Array Nat
  /-- DFS post-order: indices in the order each object's `discoverWork` returned
      (i.e. each object's `markComplete`). Built up by `markComplete`.
      At end of `discoverWith`, this is the full init order — used to
      construct `LoadGraph.initOrder`. -/
  postOrder   : Array Nat
  /-- Non-emptiness — `initial` seeds with main. -/
  sizePos     : 0 < objects.size
  /-- Names pairwise distinct — `pushObject` checks via `nameIx[name]?`. -/
  namesNodup  : (objects.map (·.name)).toList.Nodup
  /-- `deps` parallel to `objects`. -/
  depsSize    : deps.size = objects.size
  /-- Every recorded edge target is a valid object index. -/
  depsBounds  : ∀ (i : Nat) (h : i < deps.size), ∀ t ∈ deps[i], t < objects.size
  /-- `nameIx` is a faithful name→index map for `objects`. Lets dedup
      run in O(1) while invariants are stated in terms of the
      spec-level `findLoadedIdx`. -/
  nameIxValid : ∀ name : String, nameIx[name]? = findLoadedIdx objects name
  /-- `pending` parallel to `objects`. -/
  pendingSize : pending.size = objects.size
  /-- Per-row balance: `deps[i].size + pending[i] = needed_i.size`.
      Maintained by every smart constructor. Closure (`pending[i] = 0`
      for all `i`) implies `deps[i].size = needed_i.size`. -/
  rowSum      : ∀ (i : Nat) (h : i < objects.size),
    (deps[i]'(by rw [depsSize]; exact h)).size
      + (pending[i]'(by rw [pendingSize]; exact h))
      = (objects[i]'h).elf.needed.size
  /-- Every entry in `postOrder` is a valid object index. -/
  postOrderBounds : ∀ x ∈ postOrder, x < objects.size
  /-- `postOrder` has no duplicates. Combined with `postOrderBounds` and
      `postOrder.size = objects.size` (at end of DFS), this makes
      `postOrder` a permutation of `[0, objects.size)`. -/
  postOrderNodup : postOrder.toList.Nodup

namespace State

-- ============================================================================
-- Smart constructors.
-- ============================================================================

/-- Initial state: main pushed at idx 0 with an empty deps row and
    `pending[0] = mainObj.elf.needed.size`. -/
def initial (mainObj : LoadedObject) : State :=
  { objects := #[mainObj]
    deps := #[#[]]
    nameIx := (∅ : Std.HashMap String Nat).insert mainObj.name 0
    pending := #[mainObj.elf.needed.size]
    sizePos := Nat.zero_lt_one
    namesNodup := by simp
    depsSize := rfl
    depsBounds := by
      intro i h_lt t h_mem
      have h_i_zero : i = 0 := by
        have h_lt' : i < (#[#[]] : Array (Array Nat)).size := h_lt
        simp at h_lt'; omega
      subst h_i_zero
      exact absurd h_mem (by simp)
    nameIxValid := by
      intro name
      show ((∅ : Std.HashMap String Nat).insert mainObj.name 0)[name]?
            = findLoadedIdx #[mainObj] name
      have h_find : findLoadedIdx (#[mainObj] : Array LoadedObject) name
            = if mainObj.name = name then some 0 else none := by
        unfold findLoadedIdx
        show ((#[] : Array LoadedObject).push mainObj).findIdx? _ = _
        rw [Array.findIdx?_push]; simp
      rw [h_find, Std.HashMap.getElem?_insert]; simp
    pendingSize := rfl
    rowSum := by
      intro i h
      have h_i_zero : i = 0 := by
        have h_lt' : i < (#[mainObj] : Array LoadedObject).size := h
        simp at h_lt'; omega
      subst h_i_zero
      -- Goal: #[#[]][0].size + #[needed.size][0] = #[main][0].elf.needed.size
      show ((#[#[]] : Array (Array Nat))[0]).size
            + ((#[mainObj.elf.needed.size] : Array Nat)[0])
            = ((#[mainObj] : Array LoadedObject)[0]).elf.needed.size
      simp
    postOrder := #[]
    postOrderBounds := by intro x h_mem; simp at h_mem
    postOrderNodup := by simp }

/-- Push a freshly-resolved object at the next free index. The pushed
    `deps` row starts empty; subsequent `recordDep newIdx _` calls fill
    it as the DFS recurses into each `DT_NEEDED`. `pending` gets
    `obj.elf.needed.size` for the new entry — every iteration of the
    caller's `discoverWorkList` over `elf.needed.toList` decrements it. The
    `h_fresh` precondition is the `nameIx[obj.name]? = none` check
    that `discoverWork` has already done. -/
def pushObject (s : State) (obj : LoadedObject)
    (h_fresh : s.nameIx[obj.name]? = none) : State :=
  have h_find_fresh : findLoadedIdx s.objects obj.name = none :=
    (s.nameIxValid obj.name).symm.trans h_fresh
  { objects := s.objects.push obj
    deps := s.deps.push #[]
    nameIx := s.nameIx.insert obj.name s.objects.size
    pending := s.pending.push obj.elf.needed.size
    sizePos := by rw [Array.size_push]; omega
    namesNodup := nodup_names_push_of_findLoadedIdx_none s.namesNodup h_find_fresh
    depsSize := by
      show (s.deps.push #[]).size = (s.objects.push obj).size
      rw [Array.size_push, Array.size_push, s.depsSize]
    depsBounds := by
      intro i h_lt t h_mem
      have h_split : i < s.deps.size ∨ i = s.deps.size := by
        have h_lt' : i < (s.deps.push #[]).size := h_lt
        rw [Array.size_push] at h_lt'; omega
      rcases h_split with h_lt_old | h_eq
      · have h_get : (s.deps.push #[])[i]'h_lt = s.deps[i]'h_lt_old := by
          rw [Array.getElem_push, dif_pos h_lt_old]
        rw [h_get] at h_mem
        have h_t := s.depsBounds i h_lt_old t h_mem
        show t < (s.objects.push obj).size
        rw [Array.size_push]; omega
      · subst h_eq
        have h_get : (s.deps.push #[])[s.deps.size]'h_lt = (#[] : Array Nat) := by
          rw [Array.getElem_push, dif_neg (Nat.lt_irrefl _)]
        rw [h_get] at h_mem
        exact absurd h_mem (by simp)
    nameIxValid := by
      intro name
      show (s.nameIx.insert obj.name s.objects.size)[name]?
            = findLoadedIdx (s.objects.push obj) name
      rw [Std.HashMap.getElem?_insert]
      unfold findLoadedIdx
      rw [Array.findIdx?_push]
      have h_old := s.nameIxValid name
      by_cases h : obj.name = name
      · have h_find_old : s.objects.findIdx? (·.name == name) = none := by
          rw [← h]; exact h_find_fresh
        simp [h, h_find_old]
      · simp [h]
        rw [h_old]
        unfold findLoadedIdx
        cases s.objects.findIdx? (·.name == name) <;> rfl
    pendingSize := by
      show (s.pending.push obj.elf.needed.size).size = (s.objects.push obj).size
      rw [Array.size_push, Array.size_push, s.pendingSize]
    rowSum := by
      intro i h
      by_cases h_lt_old : i < s.objects.size
      · -- Old index: deps/pending/objects all use their pre-push values.
        have h_lt_d : i < s.deps.size := by rw [s.depsSize]; exact h_lt_old
        have h_lt_p : i < s.pending.size := by rw [s.pendingSize]; exact h_lt_old
        have h_deps : (s.deps.push #[])[i]'(by rw [Array.size_push, s.depsSize]; omega)
                        = s.deps[i]'h_lt_d := by
          rw [Array.getElem_push, dif_pos h_lt_d]
        have h_pend : (s.pending.push obj.elf.needed.size)[i]'(by
                        rw [Array.size_push, s.pendingSize]; omega)
                        = s.pending[i]'h_lt_p := by
          rw [Array.getElem_push, dif_pos h_lt_p]
        have h_obj : (s.objects.push obj)[i]'h = s.objects[i]'h_lt_old := by
          rw [Array.getElem_push, dif_pos h_lt_old]
        show ((s.deps.push #[])[i]'_).size
              + (s.pending.push obj.elf.needed.size)[i]'_
              = ((s.objects.push obj)[i]'h).elf.needed.size
        rw [h_deps, h_pend, h_obj]
        exact s.rowSum i h_lt_old
      · -- New index i = s.objects.size: deps[i] = #[] (size 0),
        -- pending[i] = obj.elf.needed.size, obj[i] = obj.
        have h_i_eq : i = s.objects.size := by
          have h_lt' : i < (s.objects.push obj).size := h
          rw [Array.size_push] at h_lt'; omega
        subst h_i_eq
        have h_deps : (s.deps.push #[])[s.objects.size]'(by
                        rw [Array.size_push, s.depsSize]; omega)
                        = (#[] : Array Nat) := by
          rw [Array.getElem_push, dif_neg]
          rw [s.depsSize]; exact Nat.lt_irrefl _
        have h_pend : (s.pending.push obj.elf.needed.size)[s.objects.size]'(by
                        rw [Array.size_push, s.pendingSize]; omega)
                        = obj.elf.needed.size := by
          rw [Array.getElem_push, dif_neg]
          rw [s.pendingSize]; exact Nat.lt_irrefl _
        have h_obj : (s.objects.push obj)[s.objects.size]'h = obj := by
          rw [Array.getElem_push, dif_neg (Nat.lt_irrefl _)]
        show ((s.deps.push #[])[s.objects.size]'_).size
              + (s.pending.push obj.elf.needed.size)[s.objects.size]'_
              = ((s.objects.push obj)[s.objects.size]'h).elf.needed.size
        rw [h_deps, h_pend, h_obj]
        simp
    postOrder := s.postOrder
    postOrderBounds := by
      intro x h_mem
      have h_x := s.postOrderBounds x h_mem
      show x < (s.objects.push obj).size
      rw [Array.size_push]; omega
    postOrderNodup := s.postOrderNodup }

/-- Record one dep edge `src → tgt`. Beyond the target bound, the caller
    must also discharge `src < s.objects.size` and `pending[src] > 0`
    so that `recordEdge_row_size` (which adds 1 to `deps[src].size`) and
    the decrement of `pending[src]` keep `rowSum` balanced. -/
def recordDep (s : State) (src tgt : Nat)
    (h_src : src < s.objects.size)
    (h_tgt : tgt < s.objects.size)
    (h_pending : (s.pending[src]'(by rw [s.pendingSize]; exact h_src)) > 0) :
    State :=
  { s with
    deps := recordEdge s.deps src tgt
    pending := s.pending.modify src (· - 1)
    depsSize := by rw [recordEdge_size]; exact s.depsSize
    depsBounds := recordEdge_bounds s.deps src tgt s.depsBounds h_tgt
    pendingSize := by
      show (s.pending.modify src (· - 1)).size = s.objects.size
      rw [Array.size_modify]; exact s.pendingSize
    rowSum := by
      intro i h
      -- recordEdge_row_size: deps[i].size grew by (if src = i then 1 else 0).
      -- pending modify: pending[i] = old - 1 if src = i, else unchanged.
      have h_i_d : i < s.deps.size := by rw [s.depsSize]; exact h
      have h_i_p : i < s.pending.size := by rw [s.pendingSize]; exact h
      have h_deps_size := recordEdge_row_size (deps := s.deps) (src := src) (tgt := tgt) h_i_d
      have h_pend_get :
          ((s.pending.modify src (· - 1))[i]'(by rw [Array.size_modify]; exact h_i_p))
            = (if src = i then s.pending[i]'h_i_p - 1 else s.pending[i]'h_i_p) := by
        exact Array.getElem_modify _
      have h_old := s.rowSum i h
      by_cases h_eq : src = i
      · -- src = i: deps[i].size += 1, pending[i] -= 1.
        subst h_eq
        -- After subst: `i` is replaced by `src` everywhere.
        have h_pend_pos : s.pending[src]'h_i_p > 0 := h_pending
        show ((recordEdge s.deps src tgt)[src]'_).size
              + ((s.pending.modify src (· - 1))[src]'_)
              = (s.objects[src]'h).elf.needed.size
        rw [h_deps_size, h_pend_get]
        simp
        omega
      · -- src ≠ i: both unchanged.
        show ((recordEdge s.deps src tgt)[i]'_).size
              + ((s.pending.modify src (· - 1))[i]'_)
              = (s.objects[i]'h).elf.needed.size
        rw [h_deps_size, h_pend_get]
        simp [h_eq]
        exact h_old
    postOrder := s.postOrder
    postOrderBounds := s.postOrderBounds
    postOrderNodup := s.postOrderNodup }

/-- Append `idx` to the DFS post-order. Called when an object's `discoverWork`
    is about to return — `idx` is the index of the just-finished object.
    Preconditions: idx is a valid object index, and it's not already in
    `postOrder` (so Nodup is preserved). -/
def markComplete (s : State) (idx : Nat) (h_lt : idx < s.objects.size)
    (h_fresh : idx ∉ s.postOrder.toList) : State :=
  { s with
    postOrder := s.postOrder.push idx
    postOrderBounds := by
      intro x h_mem
      rcases Array.mem_push.mp h_mem with h_old | h_eq
      · exact s.postOrderBounds x h_old
      · subst h_eq; exact h_lt
    postOrderNodup := by
      rw [Array.toList_push, List.nodup_append]
      refine ⟨s.postOrderNodup, by simp, ?_⟩
      intro a h_a b h_b h_eq_ab
      rw [List.mem_singleton] at h_b
      subst h_b
      exact h_fresh (h_eq_ab ▸ h_a) }

-- ============================================================================
-- Characterisation theorems — used by `DFS.discoverWork` / `discoverWorkList` to
-- discharge the per-iteration `WorkResult` / `WorkListAcc` invariants.
-- ============================================================================

/-- `markComplete` doesn't touch `objects`. -/
@[simp] theorem markComplete_objects_size (s : State) (idx : Nat)
    (h_lt : idx < s.objects.size) (h_fresh : idx ∉ s.postOrder.toList) :
    (s.markComplete idx h_lt h_fresh).objects.size = s.objects.size := rfl

/-- `markComplete` appends `idx` to `postOrder`. -/
@[simp] theorem markComplete_postOrder (s : State) (idx : Nat)
    (h_lt : idx < s.objects.size) (h_fresh : idx ∉ s.postOrder.toList) :
    (s.markComplete idx h_lt h_fresh).postOrder = s.postOrder.push idx := rfl

/-- `pushObject` grows `objects` by one. -/
@[simp] theorem pushObject_size (s : State) (obj : LoadedObject)
    (h_fresh : s.nameIx[obj.name]? = none) :
    (s.pushObject obj h_fresh).objects.size = s.objects.size + 1 := by
  show (s.objects.push obj).size = _
  rw [Array.size_push]

/-- `pushObject` doesn't touch `postOrder`. -/
@[simp] theorem pushObject_postOrder (s : State) (obj : LoadedObject)
    (h_fresh : s.nameIx[obj.name]? = none) :
    (s.pushObject obj h_fresh).postOrder = s.postOrder := rfl

/-- `recordDep` doesn't touch `postOrder`. -/
@[simp] theorem recordDep_postOrder (s : State) (src tgt : Nat)
    (h_src : src < s.objects.size) (h_tgt : tgt < s.objects.size)
    (h_pending : (s.pending[src]'(by rw [s.pendingSize]; exact h_src)) > 0) :
    (s.recordDep src tgt h_src h_tgt h_pending).postOrder = s.postOrder := rfl

/-- `recordDep` doesn't touch `objects`. -/
@[simp] theorem recordDep_objects_size (s : State) (src tgt : Nat)
    (h_src : src < s.objects.size) (h_tgt : tgt < s.objects.size)
    (h_pending : (s.pending[src]'(by rw [s.pendingSize]; exact h_src)) > 0) :
    (s.recordDep src tgt h_src h_tgt h_pending).objects.size = s.objects.size := rfl

/-- `recordDep` doesn't touch `pending[j]` for `j ≠ src`. -/
theorem recordDep_pending_other (s : State) (src tgt : Nat)
    (h_src : src < s.objects.size) (h_tgt : tgt < s.objects.size)
    (h_pending : (s.pending[src]'(by rw [s.pendingSize]; exact h_src)) > 0)
    (j : Nat) (h_j : j < s.objects.size) (h_ne : src ≠ j) :
    ((s.recordDep src tgt h_src h_tgt h_pending).pending[j]'(by
        show j < (s.pending.modify src (· - 1)).size
        rw [Array.size_modify, s.pendingSize]; exact h_j))
      = s.pending[j]'(by rw [s.pendingSize]; exact h_j) := by
  show ((s.pending.modify src (· - 1))[j]'_) = _
  rw [Array.getElem_modify _]
  exact if_neg h_ne

/-- At the new index, `pushObject`'s pending entry is `obj.elf.needed.size`. -/
theorem pushObject_pending_new (s : State) (obj : LoadedObject)
    (h_fresh : s.nameIx[obj.name]? = none) :
    ((s.pushObject obj h_fresh).pending[s.objects.size]'(by
        show s.objects.size < (s.pending.push obj.elf.needed.size).size
        rw [Array.size_push, s.pendingSize]; omega))
      = obj.elf.needed.size := by
  show (s.pending.push obj.elf.needed.size)[s.objects.size]'_ = _
  rw [Array.getElem_push, dif_neg]
  rw [s.pendingSize]; exact Nat.lt_irrefl _

/-- At old indices, `pushObject` doesn't change `pending`. -/
theorem pushObject_pending_old (s : State) (obj : LoadedObject)
    (h_fresh : s.nameIx[obj.name]? = none) (j : Nat) (h_j : j < s.objects.size) :
    ((s.pushObject obj h_fresh).pending[j]'(by
        show j < (s.pending.push obj.elf.needed.size).size
        rw [Array.size_push, s.pendingSize]
        exact Nat.lt_succ_of_lt h_j))
      = s.pending[j]'(by rw [s.pendingSize]; exact h_j) := by
  show (s.pending.push obj.elf.needed.size)[j]'_ = _
  rw [Array.getElem_push, dif_pos (by rw [s.pendingSize]; exact h_j)]

end State

end LeanLoad.Discover

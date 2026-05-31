/-
Discover graph construction carrier.

`Discovered` holds everything resolved so far (objects + deps) plus the
invariants we maintain as we traverse pending `WorkItem`s. Its field naming
intentionally mirrors
`LoadGraph` so the graph half of final promotion is mostly structural.

Carries the first four `LoadGraph` invariants plus the `rowSum` / `postOrder*`
invariants that `Traversal` consumes.
The fifth `LoadGraph` invariant — `closure` — is *not* carried
here; individual push/recordDep steps break it. `closure` is
established at the very end of `Finalize.discoverFrom`, when every
object's `deps` row has been fully populated.

Four smart constructors maintain the invariants:

  · `initial`       — seeds with main (idx 0).
  · `pushObject`    — adds a freshly-resolved object, empty deps row.
  · `recordDep`     — records one `src → tgt` edge.
  · `markComplete`  — appends `idx` to `postOrder` (DFS-return time).

Plus characterisation theorems (`*_size`, `*_postOrder`, `*_pending_*`)
used by `Traversal.discoverWork` / `discoverWorkList` to discharge the
`WorkResult` / `WorkListAcc` invariants they thread through the recursion.
-/

import ElfLoader.Discover.Order

namespace ElfLoader.Discover

open ElfLoader

-- ============================================================================
-- recordEdge — push a target onto deps[src]. Used by `Discovered.recordDep`.
-- ============================================================================

/-- Add an out-edge `src → tgt` to `deps`. `Array.modify` returns the
    array unchanged when `src` is out of range, but in practice every
    `src` we pass is a known-valid object index (the DFS only ever uses
    the index of an object that's already been pushed). -/
def recordEdge (deps : Array (Array Nat)) (src tgt : Nat) :
    Array (Array Nat) :=
  deps.modify src (·.push tgt)

theorem recordEdge_size (deps : Array (Array Nat)) (src tgt : Nat) :
    (recordEdge deps src tgt).size = deps.size := by
  unfold recordEdge; exact Array.size_modify

/-- Per-row size accounting: `recordEdge` grows row `src` by one and
    leaves every other row's size unchanged. Used by the DFS closure
    proof to track per-row edge growth across the foldlM over
    `elf.needed`. -/
theorem recordEdge_row_size {deps : Array (Array Nat)} {src tgt i : Nat}
    (h : i < deps.size) :
    ((recordEdge deps src tgt)[i]'(by rw [recordEdge_size]; exact h)).size =
      deps[i].size + (if src = i then 1 else 0) := by
  have h_get :
      (recordEdge deps src tgt)[i]'(by rw [recordEdge_size]; exact h) =
        if src = i then deps[i].push tgt else deps[i] := by
    unfold recordEdge
    exact Array.getElem_modify _
  rw [h_get]
  by_cases h_eq : src = i
  · simp [h_eq, Array.size_push]
  · simp [h_eq]

/-- If every existing target was `< N` and the new target is `< N`,
    then every target after `recordEdge` is `< N`. -/
theorem recordEdge_bounds (deps : Array (Array Nat)) (src tgt : Nat)
    {N : Nat}
    (h_bounds : ∀ (i : Nat) (h : i < deps.size), ∀ t ∈ deps[i], t < N)
    (h_tgt : tgt < N) :
    ∀ (i : Nat) (h : i < (recordEdge deps src tgt).size),
      ∀ t ∈ (recordEdge deps src tgt)[i], t < N := by
  intro i h_lt t h_mem
  have h_lt_orig : i < deps.size := by rw [recordEdge_size] at h_lt; exact h_lt
  have h_get :
      (recordEdge deps src tgt)[i]'h_lt =
        (if src = i then (·.push tgt) deps[i] else deps[i]) := by
    unfold recordEdge
    exact Array.getElem_modify h_lt
  rw [h_get] at h_mem
  by_cases h_eq : src = i
  · rw [if_pos h_eq] at h_mem
    rcases Array.mem_push.mp h_mem with h_old | h_eq_t
    · exact h_bounds i h_lt_orig t h_old
    · subst h_eq_t; exact h_tgt
  · rw [if_neg h_eq] at h_mem
    exact h_bounds i h_lt_orig t h_mem

-- ============================================================================
-- findDiscoveredIdx — name lookup over Array DiscoveredObject.
-- ============================================================================

/-- Linear search for an object by name. Defined via `Array.findIdx?`
    so the size bound (`findDiscoveredIdx_lt` below) drops out of the core
    `Array.of_findIdx?_eq_some` characterisation. -/
def findDiscoveredIdx (objects : Array DiscoveredObject) (name : String) : Option Nat :=
  objects.findIdx? (·.name == name)

/-- The index returned by `findDiscoveredIdx` is `< objects.size`. -/
theorem findDiscoveredIdx_lt {objects : Array DiscoveredObject} {name : String} {idx : Nat}
    (h : findDiscoveredIdx objects name = some idx) : idx < objects.size := by
  have h_match :=
    Array.of_findIdx?_eq_some (xs := objects) (p := (·.name == name)) h
  match h_get : objects[idx]? with
  | some _ =>
    obtain ⟨h_lt, _⟩ := Array.getElem?_eq_some_iff.mp h_get
    exact h_lt
  | none =>
    rw [h_get] at h_match
    exact absurd h_match (by simp)

/-- `findDiscoveredIdx = none` characterised: no object in `objects` carries
    the given name. -/
theorem findDiscoveredIdx_none_iff (objects : Array DiscoveredObject) (name : String) :
    findDiscoveredIdx objects name = none ↔ ∀ o ∈ objects, o.name ≠ name := by
  unfold findDiscoveredIdx
  rw [Array.findIdx?_eq_none_iff]
  simp

/-- Pushing a freshly-resolved object preserves the names-Nodup invariant. -/
theorem nodup_names_push_of_findDiscoveredIdx_none
    {objects : Array DiscoveredObject} {obj : DiscoveredObject}
    (h_nodup : (objects.map (·.name)).toList.Nodup)
    (h_fresh : findDiscoveredIdx objects obj.name = none) :
    ((objects.push obj).map (·.name)).toList.Nodup := by
  rw [Array.map_push, Array.toList_push, List.nodup_append]
  refine ⟨h_nodup, by simp, ?_⟩
  intro a ha b hb hab
  rw [List.mem_singleton] at hb
  subst hb
  obtain ⟨o, ho_mem, ho_name⟩ := Array.mem_map.mp (Array.mem_toList_iff.mp ha)
  have h_ne : o.name ≠ obj.name :=
    (findDiscoveredIdx_none_iff objects obj.name).mp h_fresh o ho_mem
  exact h_ne (ho_name.trans hab)

-- ============================================================================
-- Discovered — all discovered objects and partially recorded dependency edges.
-- ============================================================================

/-- Discovered-set state. Field naming intentionally mirrors `LoadGraph`
    so the graph half of final promotion (`discoverFrom`'s `LoadGraph` mk) is mostly
    structural — only `closure` is new (and falls out of `rowSum` once
    every `pending[i]` is `0`). -/
structure Discovered where
  /-- Objects discovered so far, in DFS pre-order. -/
  objects     : Array DiscoveredObject
  /-- Per-object dep edges. May be partial during DFS: row `i` is fully
      populated only after the discoverWork call that pushed `objects[i]` has
      returned. -/
  deps        : Array (Array Nat)
  /-- Per-object count of `DT_NEEDED` entries still to be recorded into
      `deps[i]`. Starts at `obj.elf.needed.size` when an object is
      pushed; decremented by `recordDep`. Tied to `deps[i].size` by
      `rowSum`. When `pending[i] = 0`, the row is complete — which is
      how `discoverFrom` discharges `LoadGraph.closure`. -/
  pending     : Array Nat
  /-- DFS post-order: indices in the order each object's `discoverWork` returned
      (i.e. each object's `markComplete`). Built up by `markComplete`.
      At end of `discoverFrom`, this is the full init order — used to
      construct `InitOrder.order`. In cyclic graphs this deterministically
      breaks active-stack back edges because gABI 08 leaves cyclic init ordering
      unspecified. -/
  postOrder   : Array Nat
  /-- Non-emptiness — `initial` seeds with main. -/
  sizePos     : 0 < objects.size
  /-- Names pairwise distinct — `pushObject` checks `findDiscoveredIdx`. -/
  namesNodup  : (objects.map (·.name)).toList.Nodup
  /-- `deps` parallel to `objects`. -/
  depsSize    : deps.size = objects.size
  /-- Every recorded edge target is a valid object index. -/
  depsBounds  : ∀ (i : Nat) (h : i < deps.size), ∀ t ∈ deps[i], t < objects.size
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
namespace Discovered

/-- Active recursion stack of object indices. The head is the current object;
    ancestors follow. A hit in this stack is a dependency cycle/back-edge; the
    traversal records it and lets DFS post-order deterministically break the
    cyclic init-order tie because gabi 08 leaves that order undefined. -/
abbrev ActiveStack := List Nat

/-- Every discovered object is either already complete (`postOrder`) or is on
    the active recursion stack. This is the key state invariant needed to
    distinguish completed dedup hits from cycle/back-edge policy failures. -/
def DoneOrActive (s : Discovered) (active : ActiveStack) : Prop :=
  ∀ i, i < s.objects.size → i ∈ s.postOrder.toList ∨ i ∈ active

/-- Every recorded edge target is either completed or active, as an immediate
    consequence of `depsBounds` and `DoneOrActive`. -/
theorem edgeTarget_done_or_active (s : Discovered) {active : ActiveStack}
    (h_active : s.DoneOrActive active)
    (i : Nat) (h_i : i < s.deps.size) (t : Nat) (h_t : t ∈ s.deps[i]) :
    t ∈ s.postOrder.toList ∨ t ∈ active :=
  h_active t (s.depsBounds i h_i t h_t)

-- ============================================================================
-- Smart constructors.
-- ============================================================================

/-- Initial state: main pushed at idx 0 with an empty deps row and
    `pending[0] = mainObj.elf.needed.size`. -/
def initial (mainObj : DiscoveredObject) : Discovered :=
  { objects := #[mainObj]
    deps := #[#[]]
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
    pendingSize := rfl
    rowSum := by
      intro i h
      have h_i_zero : i = 0 := by
        have h_lt' : i < (#[mainObj] : Array DiscoveredObject).size := h
        simp at h_lt'; omega
      subst h_i_zero
      -- Goal: #[#[]][0].size + #[needed.size][0] = #[main][0].elf.needed.size
      show ((#[#[]] : Array (Array Nat))[0]).size
            + ((#[mainObj.elf.needed.size] : Array Nat)[0])
            = ((#[mainObj] : Array DiscoveredObject)[0]).elf.needed.size
      simp
    postOrder := #[]
    postOrderBounds := by intro x h_mem; simp at h_mem
    postOrderNodup := by simp }

/-- Push a freshly-resolved object at the next free index. The pushed
    `deps` row starts empty; subsequent `recordDep newIdx _` calls fill
    it as the DFS recurses into each `DT_NEEDED`. `pending` gets
    `obj.elf.needed.size` for the new entry — every iteration of the
    caller's `discoverWorkList` over `elf.needed.toList` decrements it. -/
def pushObject (s : Discovered) (obj : DiscoveredObject)
    (h_fresh : findDiscoveredIdx s.objects obj.name = none) : Discovered :=
  { objects := s.objects.push obj
    deps := s.deps.push #[]
    pending := s.pending.push obj.elf.needed.size
    sizePos := by rw [Array.size_push]; omega
    namesNodup := nodup_names_push_of_findDiscoveredIdx_none s.namesNodup h_fresh
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
def recordDep (s : Discovered) (src tgt : Nat)
    (h_src : src < s.objects.size)
    (h_tgt : tgt < s.objects.size)
    (h_pending : (s.pending[src]'(by rw [s.pendingSize]; exact h_src)) > 0) :
    Discovered :=
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
def markComplete (s : Discovered) (idx : Nat) (h_lt : idx < s.objects.size)
    (h_fresh : idx ∉ s.postOrder.toList) : Discovered :=
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
-- Characterisation theorems — used by `Traversal.discoverWork` / `discoverWorkList` to
-- discharge the per-iteration `WorkResult` / `WorkListAcc` invariants.
-- ============================================================================

/-- `markComplete` doesn't touch `objects`. -/
@[simp] theorem markComplete_objects_size (s : Discovered) (idx : Nat)
    (h_lt : idx < s.objects.size) (h_fresh : idx ∉ s.postOrder.toList) :
    (markComplete s idx h_lt h_fresh).objects.size = s.objects.size := rfl

/-- `markComplete` appends `idx` to `postOrder`. -/
@[simp] theorem markComplete_postOrder (s : Discovered) (idx : Nat)
    (h_lt : idx < s.objects.size) (h_fresh : idx ∉ s.postOrder.toList) :
    (markComplete s idx h_lt h_fresh).postOrder = s.postOrder.push idx := rfl

/-- `pushObject` grows `objects` by one. -/
@[simp] theorem pushObject_size (s : Discovered) (obj : DiscoveredObject)
    (h_fresh : findDiscoveredIdx s.objects obj.name = none) :
    (pushObject s obj h_fresh).objects.size = s.objects.size + 1 := by
  show (s.objects.push obj).size = _
  rw [Array.size_push]

/-- `pushObject` doesn't touch `postOrder`. -/
@[simp] theorem pushObject_postOrder (s : Discovered) (obj : DiscoveredObject)
    (h_fresh : findDiscoveredIdx s.objects obj.name = none) :
    (pushObject s obj h_fresh).postOrder = s.postOrder := rfl

/-- `recordDep` doesn't touch `postOrder`. -/
@[simp] theorem recordDep_postOrder (s : Discovered) (src tgt : Nat)
    (h_src : src < s.objects.size) (h_tgt : tgt < s.objects.size)
    (h_pending : (s.pending[src]'(by rw [s.pendingSize]; exact h_src)) > 0) :
    (recordDep s src tgt h_src h_tgt h_pending).postOrder = s.postOrder := rfl

/-- `recordDep` doesn't touch `objects`. -/
@[simp] theorem recordDep_objects_size (s : Discovered) (src tgt : Nat)
    (h_src : src < s.objects.size) (h_tgt : tgt < s.objects.size)
    (h_pending : (s.pending[src]'(by rw [s.pendingSize]; exact h_src)) > 0) :
    (recordDep s src tgt h_src h_tgt h_pending).objects.size = s.objects.size := rfl

/-- `recordDep` doesn't touch `pending[j]` for `j ≠ src`. -/
theorem recordDep_pending_other (s : Discovered) (src tgt : Nat)
    (h_src : src < s.objects.size) (h_tgt : tgt < s.objects.size)
    (h_pending : (s.pending[src]'(by rw [s.pendingSize]; exact h_src)) > 0)
    (j : Nat) (h_j : j < s.objects.size) (h_ne : src ≠ j) :
    ((recordDep s src tgt h_src h_tgt h_pending).pending[j]'(by
        show j < (s.pending.modify src (· - 1)).size
        rw [Array.size_modify, s.pendingSize]; exact h_j))
      = s.pending[j]'(by rw [s.pendingSize]; exact h_j) := by
  show ((s.pending.modify src (· - 1))[j]'_) = _
  rw [Array.getElem_modify _]
  exact if_neg h_ne

/-- `recordDep` doesn't touch dep rows other than `src`. -/
theorem recordDep_deps_other (s : Discovered) (src tgt : Nat)
    (h_src : src < s.objects.size) (h_tgt : tgt < s.objects.size)
    (h_pending : (s.pending[src]'(by rw [s.pendingSize]; exact h_src)) > 0)
    (j : Nat) (h_j : j < s.objects.size) (h_ne : src ≠ j) :
    ((recordDep s src tgt h_src h_tgt h_pending).deps[j]'(by
        rw [(recordDep s src tgt h_src h_tgt h_pending).depsSize]
        exact h_j))
      = s.deps[j]'(by rw [s.depsSize]; exact h_j) := by
  show (recordEdge s.deps src tgt)[j]'_ = _
  have h_j_deps : j < s.deps.size := by rw [s.depsSize]; exact h_j
  have h_get :
      (recordEdge s.deps src tgt)[j]'(by rw [recordEdge_size]; exact h_j_deps) =
        if src = j then s.deps[j].push tgt else s.deps[j] := by
    unfold recordEdge
    exact Array.getElem_modify _
  simpa [h_ne] using h_get

/-- `pushObject` doesn't touch existing dep rows. -/
theorem pushObject_deps_old (s : Discovered) (obj : DiscoveredObject)
    (h_fresh : findDiscoveredIdx s.objects obj.name = none) (j : Nat)
    (h_j : j < s.objects.size) :
    ((pushObject s obj h_fresh).deps[j]'(by
        rw [(pushObject s obj h_fresh).depsSize]
        show j < (s.objects.push obj).size
        rw [Array.size_push]
        omega))
      = s.deps[j]'(by rw [s.depsSize]; exact h_j) := by
  show (s.deps.push #[])[j]'_ = _
  rw [Array.getElem_push, dif_pos (by rw [s.depsSize]; exact h_j)]

/-- At the new index, `pushObject`'s pending entry is `obj.elf.needed.size`. -/
theorem pushObject_pending_new (s : Discovered) (obj : DiscoveredObject)
    (h_fresh : findDiscoveredIdx s.objects obj.name = none) :
    ((pushObject s obj h_fresh).pending[s.objects.size]'(by
        show s.objects.size < (s.pending.push obj.elf.needed.size).size
        rw [Array.size_push, s.pendingSize]; omega))
      = obj.elf.needed.size := by
  show (s.pending.push obj.elf.needed.size)[s.objects.size]'_ = _
  rw [Array.getElem_push, dif_neg]
  rw [s.pendingSize]; exact Nat.lt_irrefl _

/-- At old indices, `pushObject` doesn't change `pending`. -/
theorem pushObject_pending_old (s : Discovered) (obj : DiscoveredObject)
    (h_fresh : findDiscoveredIdx s.objects obj.name = none) (j : Nat)
    (h_j : j < s.objects.size) :
    ((pushObject s obj h_fresh).pending[j]'(by
        show j < (s.pending.push obj.elf.needed.size).size
        rw [Array.size_push, s.pendingSize]
        exact Nat.lt_succ_of_lt h_j))
      = s.pending[j]'(by rw [s.pendingSize]; exact h_j) := by
  show (s.pending.push obj.elf.needed.size)[j]'_ = _
  rw [Array.getElem_push, dif_pos (by rw [s.pendingSize]; exact h_j)]

end Discovered

end ElfLoader.Discover

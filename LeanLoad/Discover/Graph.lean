/-
Graph construction helpers for Discover.

The public graph shape (`LoadedObject`, `LoadGraph`, reachability) lives in
`LeanLoad/Discover.lean`. This file keeps the lower-level array primitives and
lookup lemmas used by the internal `State` construction state.
-/

import LeanLoad.Discover

namespace LeanLoad.Discover

open LeanLoad

-- ============================================================================
-- recordEdge — push a target onto deps[src]. Used by `State.recordDep`.
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
-- findLoadedIdx — name lookup over Array LoadedObject. Free function so
-- both `LoadGraph` (final output) and `State` (State/DFS
-- construction state) can use it.
-- ============================================================================

/-- Linear search for an object by name. Defined via `Array.findIdx?`
    so the size bound (`findLoadedIdx_lt` below) drops out of the core
    `Array.of_findIdx?_eq_some` characterisation. -/
def findLoadedIdx (objects : Array LoadedObject) (name : String) : Option Nat :=
  objects.findIdx? (·.name == name)

/-- The index returned by `findLoadedIdx` is `< objects.size`. -/
theorem findLoadedIdx_lt {objects : Array LoadedObject} {name : String} {idx : Nat}
    (h : findLoadedIdx objects name = some idx) : idx < objects.size := by
  have h_match :=
    Array.of_findIdx?_eq_some (xs := objects) (p := (·.name == name)) h
  match h_get : objects[idx]? with
  | some _ =>
    obtain ⟨h_lt, _⟩ := Array.getElem?_eq_some_iff.mp h_get
    exact h_lt
  | none =>
    rw [h_get] at h_match
    exact absurd h_match (by simp)

/-- `findLoadedIdx = none` characterised: no object in `objects` carries
    the given name. -/
theorem findLoadedIdx_none_iff (objects : Array LoadedObject) (name : String) :
    findLoadedIdx objects name = none ↔ ∀ o ∈ objects, o.name ≠ name := by
  unfold findLoadedIdx
  rw [Array.findIdx?_eq_none_iff]
  simp

/-- Pushing a freshly-resolved object preserves the names-Nodup invariant.
    The precondition `findLoadedIdx = none` is what `State.pushObject`
    discharges from `nameIx[obj.name]? = none` via `nameIxValid`. -/
theorem nodup_names_push_of_findLoadedIdx_none
    {objects : Array LoadedObject} {obj : LoadedObject}
    (h_nodup : (objects.map (·.name)).toList.Nodup)
    (h_fresh : findLoadedIdx objects obj.name = none) :
    ((objects.push obj).map (·.name)).toList.Nodup := by
  rw [Array.map_push, Array.toList_push, List.nodup_append]
  refine ⟨h_nodup, by simp, ?_⟩
  intro a ha b hb hab
  rw [List.mem_singleton] at hb
  subst hb
  obtain ⟨o, ho_mem, ho_name⟩ := Array.mem_map.mp (Array.mem_toList_iff.mp ha)
  have h_ne : o.name ≠ obj.name :=
    (findLoadedIdx_none_iff objects obj.name).mp h_fresh o ho_mem
  exact h_ne (ho_name.trans hab)

end LeanLoad.Discover

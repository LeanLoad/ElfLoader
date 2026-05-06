/-
Discover-stage theorems.

Two flavours of property here:

  - `alreadyLoaded` soundness — the BFS dedup primitive returns true
    exactly when some loaded object already carries the requested name.
    Used by `Discover.discover` to terminate the BFS.

  - Structural invariants of `buildDeps` — the post-pass that resolves
    each object's `DT_NEEDED` strings to indices in `objects`. The
    parallel-array shape (`deps.size = objects.size`) and in-bounds
    property (`∀ i, ∀ j ∈ deps[i], j < objects.size`) are simple
    consequences of `Array.map` and `findIdx?` semantics. They let
    downstream proofs (Order, Reloc) drop redundant precondition
    checks.
-/

import LeanLoad.Discover

namespace LeanLoad.Thm

open LeanLoad.Discover

/-- The BFS dedup primitive returns `true` iff some loaded object
    already carries the given name. -/
theorem alreadyLoaded_iff
    (objs : Array LoadedObject) (name : String) :
    alreadyLoaded objs name = true ↔ ∃ obj ∈ objs, obj.name = name := by
  unfold alreadyLoaded
  rw [Array.any_eq_true']
  simp

/-- `buildDeps` produces an array of the same length as its input —
    parallel-array invariant for `g.objects` / `g.deps`. -/
theorem buildDeps_size (objects : Array LoadedObject) :
    (buildDeps objects).size = objects.size := by
  unfold buildDeps
  simp

/-- Every entry of `(buildDeps objects)[i]` is a valid index into
    `objects`. Follows from `findIdx?`'s in-bounds guarantee. -/
theorem buildDeps_in_bounds (objects : Array LoadedObject)
    (i : Nat) (hi : i < objects.size) (j : Nat)
    (hj : j ∈ (buildDeps objects)[i]'(by rw [buildDeps_size]; exact hi)) :
    j < objects.size := by
  unfold buildDeps at hj
  simp at hj
  obtain ⟨_, _, hfind⟩ := hj
  exact Array.findIdx?_eq_some_iff_getElem.mp hfind |>.1

/-- Dedup primitive's correctness: if the loop's invariant
    `objs.names` is `Nodup` holds and the next candidate's name passes
    the `alreadyLoaded` check (returns `false`), pushing it preserves
    the invariant. Captures the contract of the BFS dedup mechanism
    locally — the IO loop's only job is to use this primitive
    correctly before each push. -/
theorem nodup_names_push_of_alreadyLoaded_false
    (objs : Array LoadedObject) (obj : LoadedObject)
    (h_nodup : (objs.map (·.name)).toList.Nodup)
    (h_fresh : alreadyLoaded objs obj.name = false) :
    ((objs.push obj).map (·.name)).toList.Nodup := by
  rw [Array.map_push, Array.toList_push, List.nodup_append]
  refine ⟨h_nodup, by simp, ?_⟩
  intro a ha b hb hab
  rw [List.mem_singleton] at hb
  subst hb
  have h_in : ∃ o ∈ objs, o.name = obj.name := by
    obtain ⟨o, ho_mem, ho_name⟩ := Array.mem_map.mp (Array.mem_toList_iff.mp ha)
    exact ⟨o, ho_mem, ho_name.trans hab⟩
  exact (Bool.eq_false_iff.mp h_fresh) ((alreadyLoaded_iff objs obj.name).mpr h_in)

end LeanLoad.Thm

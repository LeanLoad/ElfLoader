/-
Discover-stage theorems.

  - `alreadyLoaded` soundness — the BFS dedup primitive returns true
    exactly when some loaded object already carries the requested name.
    Used by `Discover.discover` to terminate the BFS.

  - The dedup-pushes-stay-Nodup lemma, capturing the contract of the
    BFS dedup mechanism: if `alreadyLoaded` says `false`, pushing
    preserves the name-uniqueness invariant.

The `buildDeps` size + in-bounds invariants used to live here too,
but `buildDeps` has moved to `LeanLoad.InitPlan` (init/fini are its
only consumer). Its theorems live in `LeanLoad.Thm.InitPlan`.
-/

import LeanLoad.DiscoverPlan

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

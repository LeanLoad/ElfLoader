/-
Discover-stage theorems (partial).

`alreadyLoaded` is the BFS dedup primitive — `Discover.discover`
calls it before resolving each `DT_NEEDED` entry, and again after
canonicalisation, to avoid loading the same object twice. The
soundness lemma here is the contract: it returns `true` exactly
when some loaded object already carries the requested name.
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

end LeanLoad.Thm

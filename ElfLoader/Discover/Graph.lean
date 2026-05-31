/-
Dependency-graph facts for Discover.
-/

import ElfLoader.Discover

namespace ElfLoader.Discover

namespace LoadGraph

/-- A dependency edge's source is a valid object index. -/
theorem Step.src_lt_objects (g : LoadGraph) {i j : Nat} (h : g.Step i j) :
    i < g.objects.size := by
  rcases h with ⟨h_i, _h_j⟩
  rw [← g.depsSize]
  exact h_i

/-- A dependency edge's target is a valid object index. -/
theorem Step.tgt_lt_objects (g : LoadGraph) {i j : Nat} (h : g.Step i j) :
    j < g.objects.size := by
  rcases h with ⟨h_i, h_j⟩
  exact g.depsBounds i h_i j h_j

/-- Reachability from a valid source stays inside the graph. -/
theorem Reachable.tgt_lt_objects (g : LoadGraph) {i j : Nat}
    (h_i : i < g.objects.size) (h : g.Reachable i j) :
    j < g.objects.size := by
  induction h with
  | refl => exact h_i
  | tail _h_ij h_jk _ih => exact Step.tgt_lt_objects g h_jk

/-- Anything reachable from main is a valid object index. -/
theorem ReachableFromMain.lt_objects (g : LoadGraph) {i : Nat}
    (h : g.ReachableFromMain i) : i < g.objects.size := by
  unfold ReachableFromMain at h
  exact Reachable.tgt_lt_objects g g.sizePos h

end LoadGraph

end ElfLoader.Discover

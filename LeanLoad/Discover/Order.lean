/-
Init-order predicates used while building and after finalizing an `InitOrder`.
-/

import LeanLoad.Discover

namespace LeanLoad.Discover

namespace LoadGraph

private theorem List.getElem?_eq_some_inj_of_nodup {α : Type u} {xs : List α}
    (h_nodup : xs.Nodup) :
    ∀ {i j : Nat} {a : α}, xs[i]? = some a → xs[j]? = some a → i = j := by
  induction xs with
  | nil =>
      intro i _j _a hi _hj
      cases i <;> simp at hi
  | cons x xs ih =>
      rw [List.nodup_cons] at h_nodup
      rcases h_nodup with ⟨h_not_mem, h_tail⟩
      intro i j a hi hj
      cases i with
      | zero =>
          cases j with
          | zero => rfl
          | succ j =>
              simp at hi
              have h_mem : a ∈ xs := by
                rw [List.mem_iff_getElem?]
                exact ⟨j, hj⟩
              exact False.elim (h_not_mem (hi.symm ▸ h_mem))
      | succ i =>
          cases j with
          | zero =>
              simp at hj
              have h_mem : a ∈ xs := by
                rw [List.mem_iff_getElem?]
                exact ⟨i, hi⟩
              exact False.elim (h_not_mem (hj.symm ▸ h_mem))
          | succ j =>
              simp at hi hj
              exact congrArg Nat.succ (ih h_tail hi hj)

/-- The left endpoint of a `PostBefore` witness appears in the order. -/
theorem PostBefore.left_mem {order : Array Nat} {a b : Nat}
    (h : PostBefore order a b) : a ∈ order.toList := by
  rcases h with ⟨ia, _ib, hia, _hib, _hlt⟩
  exact Array.mem_toList_iff.mpr (Array.mem_iff_getElem?.mpr ⟨ia, hia⟩)

/-- The right endpoint of a `PostBefore` witness appears in the order. -/
theorem PostBefore.right_mem {order : Array Nat} {a b : Nat}
    (h : PostBefore order a b) : b ∈ order.toList := by
  rcases h with ⟨_ia, ib, _hia, hib, _hlt⟩
  exact Array.mem_toList_iff.mpr (Array.mem_iff_getElem?.mpr ⟨ib, hib⟩)

/-- If `a` is already present, then appending `b` places `a` before `b`. -/
theorem PostBefore.push_right {order : Array Nat} {a b : Nat}
    (ha : a ∈ order.toList) : PostBefore (order.push b) a b := by
  have ha_arr : a ∈ order := Array.mem_toList_iff.mp ha
  obtain ⟨ia, hia⟩ := Array.mem_iff_getElem?.mp ha_arr
  have hia_lt : ia < order.size := by
    obtain ⟨h, _⟩ := Array.getElem?_eq_some_iff.mp hia
    exact h
  refine ⟨ia, order.size, ?_, ?_, hia_lt⟩
  · rw [Array.getElem?_push]
    have h_ne : ia ≠ order.size := Nat.ne_of_lt hia_lt
    rw [if_neg h_ne]
    exact hia
  · rw [Array.getElem?_push, if_pos rfl]

/-- Appending one more index preserves an existing before relation. -/
theorem PostBefore.push_preserved {order : Array Nat} {a b c : Nat}
    (h : PostBefore order a b) : PostBefore (order.push c) a b := by
  rcases h with ⟨ia, ib, hia, hib, hlt⟩
  have hia_lt : ia < order.size := (Array.getElem?_eq_some_iff.mp hia).1
  have hib_lt : ib < order.size := (Array.getElem?_eq_some_iff.mp hib).1
  refine ⟨ia, ib, ?_, ?_, hlt⟩
  · rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hia_lt)]
    exact hia
  · rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hib_lt)]
    exact hib

/-- A value has at most one index in a duplicate-free array. -/
theorem index_unique_of_nodup {order : Array Nat} (h_nodup : order.toList.Nodup)
    {i j a : Nat} (hi : order[i]? = some a) (hj : order[j]? = some a) : i = j := by
  exact List.getElem?_eq_some_inj_of_nodup h_nodup (by simpa using hi) (by simpa using hj)

/-- In a duplicate-free order, `PostBefore order a b` implies `a ≠ b`. -/
theorem PostBefore.ne_of_nodup {order : Array Nat} (h_nodup : order.toList.Nodup)
    {a b : Nat} (h : PostBefore order a b) : a ≠ b := by
  rcases h with ⟨ia, ib, hia, hib, hlt⟩
  intro h_eq
  have h_idx : ia = ib := by
    exact index_unique_of_nodup h_nodup hia (by simpa [h_eq] using hib)
  omega

/-- A duplicate-free order cannot place `a` before `b` and `b` before `a`. -/
theorem PostBefore.not_reverse_of_nodup {order : Array Nat} (h_nodup : order.toList.Nodup)
    {a b : Nat} (h : PostBefore order a b) : ¬ PostBefore order b a := by
  rcases h with ⟨ia, ib, hia, hib, hlt⟩
  intro h_rev
  rcases h_rev with ⟨ib', ia', hib', hia', hlt'⟩
  have h_ib : ib' = ib := index_unique_of_nodup h_nodup hib' hib
  have h_ia : ia' = ia := index_unique_of_nodup h_nodup hia' hia
  omega

end LoadGraph

namespace InitOrder

/-- `a` appears before `b` in this init order.

    The arguments are `Fin g.objects.size`, so the index-in-bounds part of the
    init-order invariant is carried by the type. -/
def InitBefore {g : LoadGraph} (init : InitOrder g) (a b : Fin g.objects.size) : Prop :=
  ∃ ia ib : Nat,
    init.order[ia]? = some a ∧
    init.order[ib]? = some b ∧
    ia < ib

/-- Nat-index wrapper around `InitBefore`, useful when working from `g.Step`
    edges, whose endpoints are Nat-valued. Bounds are carried by the `Fin`
    entries inside `initOrder`; this wrapper intentionally compares their
    underlying natural indices. -/
def InitBeforeIdx {g : LoadGraph} (init : InitOrder g) (a b : Nat) : Prop :=
  LoadGraph.PostBefore (init.order.map (fun ix => ix.val)) a b

/-- Every object index appears in `init.order`. Bounds are carried by the `Fin`
    entries; this predicate names the coverage half of the init-order
    permutation witness. -/
def Covers {g : LoadGraph} (init : InitOrder g) : Prop :=
  ∀ i, i < g.objects.size → i ∈ (init.order.map (fun ix => ix.val)).toList

/-- Init-order topological property for produced graphs.

    For a direct dependency edge `i → j`, the dependency `j` appears before its
    dependent `i`. Discover rejects active-stack cycles while building the graph;
    gabi 08 leaves cyclic init ordering undefined. -/
def RespectsDeps {g : LoadGraph} (init : InitOrder g) : Prop :=
  ∀ i j, g.Step i j → init.InitBeforeIdx j i

theorem covers_spec {g : LoadGraph} (init : InitOrder g) :
    init.Covers :=
  init.covers

theorem respectsDeps_spec {g : LoadGraph} (init : InitOrder g) :
    init.RespectsDeps := by
  intro i j h_step
  exact init.respectsDeps i j h_step

/-- Every value in an `InitOrder` is a valid object index. -/
theorem mem_lt_objects {g : LoadGraph} (init : InitOrder g) {i : Nat}
    (h_mem : i ∈ (init.order.map (fun ix => ix.val)).toList) :
    i < g.objects.size := by
  rw [Array.toList_map] at h_mem
  rw [List.mem_map] at h_mem
  rcases h_mem with ⟨ix, _h_ix_mem, h_eq⟩
  rw [← h_eq]
  exact ix.isLt

/-- `InitOrder.covers` plus Fin-typed entries characterises order membership. -/
theorem mem_iff_lt_objects {g : LoadGraph} (init : InitOrder g) {i : Nat} :
    i ∈ (init.order.map (fun ix => ix.val)).toList ↔ i < g.objects.size := by
  constructor
  · exact init.mem_lt_objects
  · intro h_lt
    exact init.covers i h_lt

/-- The left endpoint of an init-before relation is a valid object index. -/
theorem InitBeforeIdx.left_lt_objects {g : LoadGraph} (init : InitOrder g) {a b : Nat}
    (h : init.InitBeforeIdx a b) : a < g.objects.size :=
  init.mem_lt_objects (LoadGraph.PostBefore.left_mem h)

/-- The right endpoint of an init-before relation is a valid object index. -/
theorem InitBeforeIdx.right_lt_objects {g : LoadGraph} (init : InitOrder g) {a b : Nat}
    (h : init.InitBeforeIdx a b) : b < g.objects.size :=
  init.mem_lt_objects (LoadGraph.PostBefore.right_mem h)

/-- A duplicate-free init order cannot put one index before itself. -/
theorem InitBeforeIdx.ne {g : LoadGraph} (init : InitOrder g) {a b : Nat}
    (h : init.InitBeforeIdx a b) : a ≠ b := by
  exact LoadGraph.PostBefore.ne_of_nodup
    (by simpa [Array.toList_map] using init.nodup) h

/-- A duplicate-free init order cannot place `a` before `b` and `b` before `a`. -/
theorem InitBeforeIdx.not_reverse {g : LoadGraph} (init : InitOrder g) {a b : Nat}
    (h : init.InitBeforeIdx a b) : ¬ init.InitBeforeIdx b a := by
  exact LoadGraph.PostBefore.not_reverse_of_nodup
    (by simpa [Array.toList_map] using init.nodup) h

/-- A certified init order rules out direct self-dependencies. -/
theorem step_ne {g : LoadGraph} (init : InitOrder g) {i j : Nat}
    (h : g.Step i j) : j ≠ i := by
  exact InitBeforeIdx.ne init (init.respectsDeps_spec i j h)

/-- A certified init order rules out direct two-node dependency cycles. -/
theorem step_not_reverse {g : LoadGraph} (init : InitOrder g) {i j : Nat}
    (h : g.Step i j) : ¬ g.Step j i := by
  have h_before := init.respectsDeps_spec i j h
  intro h_rev
  exact InitBeforeIdx.not_reverse init h_before (init.respectsDeps_spec j i h_rev)

end InitOrder

end LeanLoad.Discover

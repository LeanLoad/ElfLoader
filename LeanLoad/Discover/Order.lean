/-
Init-order predicates used while building and after finalizing an `InitOrder`.
-/

import LeanLoad.Discover.Basic

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

/-- `a` appears before `b` in an array of natural indices. This is the raw
    postorder relation used before `InitOrder.order` wraps indices as `Fin`s. -/
def PostBefore (order : Array Nat) (a b : Nat) : Prop :=
  ∃ ia ib : Nat,
    order[ia]? = some a ∧
    order[ib]? = some b ∧
    ia < ib

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

end LeanLoad.Discover

/-
Order-stage theorems.

`g.order` (DFS post-order over `DT_NEEDED`) satisfies three structural
invariants, all derived from a single inductive invariant `Inv`
threaded through `dfs` and the inner `Array.foldl`:

  - `dfs_visited_monotonic` — once a bit is set, no recursive call clears it.
  - `order_in_bounds`       — every `i ∈ g.order` has `i < g.objects.size`.
  - `order_no_duplicates`   — `g.order.toList.Nodup`.
  - `order_size_le`         — corollary of the previous two.

Together these are the load-bearing facts for downstream proofs that
quantify over "the objects we initialise".
-/

import LeanLoad.Order

namespace LeanLoad.Thm

open LeanLoad.Order
open LeanLoad.Discover

/-- Combined `dfs` invariant: `visited` has the expected size, every
    emitted index is in-bounds with its visited bit set, and `order`
    has no duplicates. -/
def Inv (n : Nat) (visited : Array Bool) (order : Array Nat) : Prop :=
  visited.size = n ∧
  order.toList.Nodup ∧
  ∀ i, i ∈ order → ∃ h : i < visited.size, visited[i] = true

/-- `Array.foldl` over `dfs` preserves the first-component size of the
    accumulator. Helper for `dfs_visited_size`. -/
private theorem foldl_dfs_size (fuel : Nat) (g : DepGraph)
    (children : Array Nat) (visited : Array Bool) (order : Array Nat)
    (ih : ∀ (idx : Nat) (v : Array Bool) (o : Array Nat),
            (dfs fuel g idx v o).1.size = v.size) :
    (children.foldl (fun st c => dfs fuel g c st.1 st.2) (visited, order)).1.size
      = visited.size := by
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (st : Array Bool × Array Nat) =>
                 st.1.size = visited.size)
  · rfl
  · intro i st hst
    show (dfs fuel g _ st.1 st.2).1.size = visited.size
    rw [ih]; exact hst

/-- `dfs` preserves `visited.size` (only ever uses `Array.set`). -/
theorem dfs_visited_size (fuel : Nat) (g : DepGraph) (idx : Nat)
    (visited : Array Bool) (order : Array Nat) :
    (dfs fuel g idx visited order).1.size = visited.size := by
  induction fuel generalizing idx visited order with
  | zero => unfold dfs; rfl
  | succ fuel ih =>
    unfold dfs
    split
    · split
      · rfl
      · simp only
        rw [foldl_dfs_size fuel g _ _ _ ih, Array.size_set]
    · rfl

/-- Wrap `arr[i] = v` (dependent) as `arr[i]? = some v` (non-dependent). -/
private theorem some_of_getElem {α} {arr : Array α} {i : Nat} {v : α}
    (hi : i < arr.size) (hv : arr[i] = v) : arr[i]? = some v := by
  rw [Array.getElem?_eq_getElem hi, hv]

/-- `Array.foldl` over `dfs` preserves "this index is set to true".
    Helper for `dfs_visited_monotonic`. -/
private theorem foldl_dfs_monotonic (fuel : Nat) (g : DepGraph)
    (children : Array Nat) (visited : Array Bool) (order : Array Nat) (i : Nat)
    (hi : i < visited.size) (hv : visited[i] = true)
    (ih : ∀ (idx : Nat) (v : Array Bool) (o : Array Nat),
            (h : i < v.size) → v[i] = true →
            (dfs fuel g idx v o).1[i]? = some true) :
    (children.foldl (fun st c => dfs fuel g c st.1 st.2) (visited, order)).1[i]?
      = some true := by
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (st : Array Bool × Array Nat) =>
                 st.1[i]? = some true)
  · exact some_of_getElem hi hv
  · intro _ st hst
    obtain ⟨hsi, hvi⟩ := Array.getElem?_eq_some_iff.mp hst
    show (dfs fuel g _ st.1 st.2).1[i]? = some true
    exact ih _ st.1 st.2 hsi hvi

/-- Once a visited bit is set, no recursive `dfs` call clears it. The
    monotonicity lemma underpinning the push-step Nodup argument.

    Stated via `[i]?` to keep the bound non-dependent: combined with
    `dfs_visited_size` it gives the dependent form. -/
theorem dfs_visited_monotonic (fuel : Nat) (g : DepGraph) (idx : Nat)
    (visited : Array Bool) (order : Array Nat) (i : Nat)
    (hi : i < visited.size) (hv : visited[i] = true) :
    (dfs fuel g idx visited order).1[i]? = some true := by
  induction fuel generalizing idx visited order with
  | zero => unfold dfs; exact some_of_getElem hi hv
  | succ fuel ih =>
    unfold dfs
    split
    · split
      · exact some_of_getElem hi hv
      · next h1 _ =>
        simp only
        have hi' : i < (visited.set idx true h1).size := by
          rw [Array.size_set]; exact hi
        have hv' : (visited.set idx true h1)[i] = true := by
          by_cases heq : i = idx
          · subst heq; simp
          · rw [Array.getElem_set]; simp [hv]
        exact foldl_dfs_monotonic fuel g _ _ order i hi' hv' ih
    · exact some_of_getElem hi hv

/-- `dfs` preserves Nodup-style "this index is not in order" if its
    visited bit is already set. The push-step disjointness lemma. -/
private theorem foldl_dfs_no_membership (fuel : Nat) (g : DepGraph)
    (children : Array Nat) (visited : Array Bool) (order : Array Nat) (j : Nat)
    (hj_size : j < visited.size) (hj_visited : visited[j] = true) (hj_order : j ∉ order)
    (ih : ∀ (idx : Nat) (v : Array Bool) (o : Array Nat)
            (hjs : j < v.size), v[j] = true → j ∉ o →
            j ∉ (dfs fuel g idx v o).2) :
    j ∉ (children.foldl (fun st c => dfs fuel g c st.1 st.2) (visited, order)).2 := by
  -- Combined motive: (st.1[j]? = some true) ∧ (j ∉ st.2). The first part is preserved
  -- by monotonicity (already proved); the second by ih.
  suffices h :
      (children.foldl (fun st c => dfs fuel g c st.1 st.2) (visited, order)).1[j]?
        = some true ∧
      j ∉ (children.foldl (fun st c => dfs fuel g c st.1 st.2) (visited, order)).2
    from h.2
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (st : Array Bool × Array Nat) =>
                 st.1[j]? = some true ∧ j ∉ st.2)
  · exact ⟨some_of_getElem hj_size hj_visited, hj_order⟩
  · intro _ st ⟨hv?, ho⟩
    obtain ⟨hjs, hjv⟩ := Array.getElem?_eq_some_iff.mp hv?
    refine ⟨?_, ih _ st.1 st.2 hjs hjv ho⟩
    exact dfs_visited_monotonic fuel g _ st.1 st.2 j hjs hjv

/-- If an index is already marked visited and not in `order`, `dfs`
    won't add it. The structural lemma for the Nodup push-step. -/
theorem dfs_preserves_no_membership (fuel : Nat) (g : DepGraph) (idx : Nat)
    (visited : Array Bool) (order : Array Nat) (j : Nat)
    (hj_size : j < visited.size) (hj_visited : visited[j] = true) (hj_order : j ∉ order) :
    j ∉ (dfs fuel g idx visited order).2 := by
  induction fuel generalizing idx visited order with
  | zero => unfold dfs; exact hj_order
  | succ fuel ih =>
    unfold dfs
    split
    · split
      · exact hj_order
      · next h1 h2 =>
        simp only
        have hne : idx ≠ j := fun heq => h2 (heq ▸ hj_visited)
        have hjs' : j < (visited.set idx true h1).size := by
          rw [Array.size_set]; exact hj_size
        have hjv' : (visited.set idx true h1)[j] = true := by
          rw [Array.getElem_set]; simp [hne, hj_visited]
        have hno_foldl :=
          foldl_dfs_no_membership fuel g (g.deps[idx]?.getD #[])
            (visited.set idx true h1) order j hjs' hjv' hj_order ih
        intro hin
        rw [Array.mem_push] at hin
        rcases hin with hin | hin
        · exact hno_foldl hin
        · exact hne hin.symm
    · exact hj_order

/-- `visited.set idx true` preserves `Inv`. Step 1 of `dfs_preserves_inv`. -/
private theorem inv_set_visited {n : Nat} {visited : Array Bool} {order : Array Nat}
    (idx : Nat) (hi : idx < visited.size) (h : Inv n visited order) :
    Inv n (visited.set idx true hi) order := by
  obtain ⟨hs, hn, hb⟩ := h
  refine ⟨by simp [hs], hn, ?_⟩
  intro k hk
  obtain ⟨hks, hkv⟩ := hb k hk
  refine ⟨by simp [hks], ?_⟩
  by_cases heq : k = idx
  · subst heq; simp
  · rw [Array.getElem_set]; simp [hkv]

/-- `Array.foldl` over `dfs` preserves `Inv`. Step 2 of `dfs_preserves_inv`. -/
private theorem foldl_dfs_preserves_inv {n : Nat} (fuel : Nat) (g : DepGraph)
    (children : Array Nat) (visited : Array Bool) (order : Array Nat)
    (h : Inv n visited order) (heq : n = g.objects.size)
    (ih : ∀ (idx : Nat) (v : Array Bool) (o : Array Nat),
            Inv g.objects.size v o →
            Inv g.objects.size (dfs fuel g idx v o).1 (dfs fuel g idx v o).2) :
    Inv n
      (children.foldl (fun st c => dfs fuel g c st.1 st.2) (visited, order)).1
      (children.foldl (fun st c => dfs fuel g c st.1 st.2) (visited, order)).2 := by
  subst heq
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (st : Array Bool × Array Nat) =>
                 Inv g.objects.size st.1 st.2)
  · exact h
  · intro _ st hst
    show Inv g.objects.size (dfs fuel g _ st.1 st.2).1 (dfs fuel g _ st.1 st.2).2
    exact ih _ _ _ hst

/-- `order.push idx` preserves `Inv` when `idx` is a fresh, in-bounds,
    visited index. Step 3 of `dfs_preserves_inv`. -/
private theorem inv_push {n : Nat} {visited : Array Bool} {order : Array Nat}
    (idx : Nat) (h : Inv n visited order) (hi : idx < visited.size)
    (hv : visited[idx] = true) (hno : idx ∉ order) :
    Inv n visited (order.push idx) := by
  obtain ⟨hs, hn, hb⟩ := h
  refine ⟨hs, ?_, ?_⟩
  · rw [Array.toList_push, List.nodup_append]
    refine ⟨hn, by simp, ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton] at hb
    subst hb
    exact hno (Array.mem_toList_iff.mp (hab ▸ ha))
  · intro k hk
    rw [Array.mem_push] at hk
    rcases hk with hkin | rfl
    · exact hb k hkin
    · exact ⟨hi, hv⟩

/-- `dfs` preserves `Inv`. Composition of the three step lemmas. -/
theorem dfs_preserves_inv (fuel : Nat) (g : DepGraph) (idx : Nat)
    (visited : Array Bool) (order : Array Nat)
    (h : Inv g.objects.size visited order) :
    Inv g.objects.size (dfs fuel g idx visited order).1
                       (dfs fuel g idx visited order).2 := by
  induction fuel generalizing idx visited order with
  | zero => unfold dfs; exact h
  | succ fuel ih =>
    unfold dfs
    split
    · split
      · exact h
      · next h1 h2 =>
        simp only
        -- (1) set visited[idx] := true; (2) foldl over deps; (3) push idx.
        let children := g.deps[idx]?.getD #[]
        have hInv1 := inv_set_visited idx h1 h
        have hInv2 := foldl_dfs_preserves_inv fuel g children _ order hInv1 rfl ih
        have hno_orig : idx ∉ order := fun hin => h2 (h.2.2 idx hin).2
        have hsz_set : idx < (visited.set idx true h1).size := by simp [h1]
        have hvi_set : (visited.set idx true h1)[idx] = true := by simp
        have hno_foldl :=
          foldl_dfs_no_membership fuel g children _ order idx hsz_set hvi_set hno_orig
            (fun idx' v o hjs hvi' hno' =>
               dfs_preserves_no_membership fuel g idx' v o idx hjs hvi' hno')
        have hmono :=
          foldl_dfs_monotonic fuel g children _ order idx hsz_set hvi_set
            (fun idx' v o hjs hvi' =>
               dfs_visited_monotonic fuel g idx' v o idx hjs hvi')
        obtain ⟨hsz_foldl, hvi_foldl⟩ := Array.getElem?_eq_some_iff.mp hmono
        exact inv_push idx hInv2 hsz_foldl hvi_foldl hno_foldl
    · exact h

/-- The seed for `dfs n g 0`: empty `order`, all-false `visited`. -/
private theorem inv_seed (g : DepGraph) :
    Inv g.objects.size (Array.replicate g.objects.size false) (Array.mkEmpty g.objects.size) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Array.size_replicate]
  · simp
  · intro i hi
    simp at hi

/-- Every entry of `g.order` is a valid object index. -/
theorem order_in_bounds (g : DepGraph) (i : Nat) (hi : i ∈ g.order) :
    i < g.objects.size := by
  unfold DepGraph.order at hi
  by_cases hN : g.objects.size = 0
  · simp [hN] at hi
  · simp [hN] at hi
    have hpres := dfs_preserves_inv g.objects.size g 0 _ _ (inv_seed g)
    obtain ⟨hsize, _, hbnd⟩ := hpres
    obtain ⟨hb, _⟩ := hbnd i hi
    rw [hsize] at hb
    exact hb

/-- `g.order` has no duplicate indices. -/
theorem order_no_duplicates (g : DepGraph) : g.order.toList.Nodup := by
  unfold DepGraph.order
  by_cases hN : g.objects.size = 0
  · simp [hN]
  · simp [hN]
    exact (dfs_preserves_inv g.objects.size g 0 _ _ (inv_seed g)).2.1

/-- A `Nodup` list of `Nat`s all `< n` has length `≤ n`. Used to lift
    `order_no_duplicates` + `order_in_bounds` into a size bound. -/
private theorem nodup_lt_length_le : ∀ (n : Nat) {l : List Nat},
    l.Nodup → (∀ i ∈ l, i < n) → l.length ≤ n
  | 0,     l, _,   hb => by
    cases l with
    | nil       => simp
    | cons x _  => exact absurd (hb x List.mem_cons_self) (Nat.not_lt_zero _)
  | n + 1, l, hno, hb => by
    by_cases hn : n ∈ l
    · have hno_e : (l.erase n).Nodup := by
        rw [List.erase_eq_eraseP]; exact hno.eraseP _
      have hlen : (l.erase n).length = l.length - 1 := by
        rw [List.length_erase]; simp [hn]
      have hb_e : ∀ i ∈ l.erase n, i < n := by
        intro i hi
        obtain ⟨hne, hin⟩ := hno.mem_erase_iff.mp hi
        have : i < n + 1 := hb i hin
        omega
      have ih := nodup_lt_length_le n hno_e hb_e
      have hpos : l.length ≥ 1 := by
        cases l with
        | nil      => exact absurd hn (List.not_mem_nil)
        | cons _ _ => simp
      omega
    · have hb' : ∀ i ∈ l, i < n := by
        intro i hi
        have hlt : i < n + 1 := hb i hi
        have hne : i ≠ n := fun heq => hn (heq ▸ hi)
        omega
      have ih := nodup_lt_length_le n hno hb'
      omega

/-- Bounded indices + no duplicates ⇒ `g.order.size ≤ g.objects.size`. -/
theorem order_size_le_objects_size (g : DepGraph) :
    g.order.size ≤ g.objects.size := by
  rw [← Array.length_toList]
  apply nodup_lt_length_le g.objects.size (order_no_duplicates g)
  intro i hi
  exact order_in_bounds g i (Array.mem_toList_iff.mp hi)

end LeanLoad.Thm

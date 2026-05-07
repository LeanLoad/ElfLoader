/-
Layout-stage spec theorems — kept for auditability, not consumed by
the runtime path.

  - `segment_endAddr_le_objectSpan` — every segment's `endAddr` is
    bounded by the layout's `objectSpan` (the `foldl max 0` upper
    bound), which `Plan/Layout.assignBases` relies on for its slot
    arithmetic.
  - `segmentsPairwiseDisjoint_of_segmentsSorted` — sorted
    `[vaddr, endAddr)` ranges are pairwise disjoint. This is the
    safety property that justifies the loader's `MAP_FIXED` mmaps:
    no two PT_LOADs collide.
  - `segmentsSortedB_iff_segmentsSorted` — Bool ↔ Prop bridge for
    `segmentsSortedB := decide segmentsSorted`. Trivial after that
    refactor; kept as the explicit handle for spec consumers.
  - `layouts_segmentsPairwiseDisjoint` — pairwise disjointness for
    every layout in `g.layouts`'s success branch, via the
    `segmentsSorted` witness packed into the return subtype.

`g.layouts` either rejects an ELF whose page-aligned `PT_LOAD` ranges
are not sorted/non-overlapping, or returns a witness that they are.
gabi 07 mandates the underlying sort; the page-disjoint property is
a layout-level concern (linkers produce it; the runtime check above
enforces it).
-/

import LeanLoad.Plan.Layout

namespace LeanLoad.Thm

open LeanLoad.Layout
open LeanLoad.Discover
open LeanLoad.Elaborate

/-- Each segment's `endAddr` is bounded by its object's `objectSpan`.
    The `foldl max 0` upper-bound, lifted to every input element. -/
theorem segment_endAddr_le_objectSpan
    (lyt : ObjectLayout) (i : Nat) (h : i < lyt.segments.size) :
    lyt.segments[i].pageEndAddr ≤ objectSpan lyt.segments := by
  let motive : Nat → UInt64 → Prop := fun n acc =>
    ∀ k (_ : k < n) (_ : k < lyt.segments.size),
      lyt.segments[k].pageEndAddr ≤ acc
  suffices motive lyt.segments.size (objectSpan lyt.segments) from this i h h
  unfold objectSpan
  refine Array.foldl_induction motive ?_ ?_
  · intros _ hk _; omega
  · intro idx b ih k hk hk'
    by_cases hkj : k = idx.val
    · have hindex : lyt.segments[k] = lyt.segments[idx] := by congr 1
      rw [hindex]
      show _ ≤ ite _ _ _
      split
      · exact UInt64.le_refl _
      · rename_i hnle; exact (UInt64.le_total b _).resolve_left hnle
    · have hk_lt : k < idx.val :=
        Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk) hkj
      have prev_le : lyt.segments[k].pageEndAddr ≤ b := ih k hk_lt hk'
      show _ ≤ ite _ _ _
      split
      · rename_i hb_le; exact UInt64.le_trans prev_le hb_le
      · exact prev_le

-- ============================================================================
-- Alignment-arithmetic lemmas. These belong here (and not on the
-- definitions in `Plan.Layout`) since the proof artifacts aren't
-- consumed by the runtime path; they exist for downstream proofs to
-- close `Region.InRange` etc. without runtime checks.
-- ============================================================================

/-- `alignDown` rounds toward zero: `alignDown x align ≤ x`. -/
theorem alignDown_le (x align : UInt64) : alignDown x align ≤ x := by
  unfold alignDown
  split
  · exact UInt64.le_refl _
  · have h_mod_le : x % align ≤ x := by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
      exact Nat.mod_le _ _
    exact UInt64.sub_le h_mod_le

private theorem toNat_pos_of_ne_zero {a : UInt64} (h : a ≠ 0) : 0 < a.toNat := by
  rcases Nat.eq_zero_or_pos a.toNat with h0 | hp
  · exfalso; apply h; exact UInt64.toNat_inj.mp (h0.trans rfl.symm)
  · exact hp

/-- `alignUp` rounds away from zero: `x ≤ alignUp x align`, given `align`
    is non-zero and `x + align` fits in UInt64 (no wrap). -/
theorem alignUp_ge (x align : UInt64)
    (h_align_ne : align ≠ 0)
    (h_bound : x.toNat + align.toNat < 2^64) : x ≤ alignUp x align := by
  unfold alignUp
  rw [if_neg (by intro h; exact h_align_ne (by simpa using h))]
  unfold alignDown
  rw [if_neg (by intro h; exact h_align_ne (by simpa using h))]
  have h_align_pos : 0 < align.toNat := toNat_pos_of_ne_zero h_align_ne
  have h_xa : (x + align).toNat = x.toNat + align.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_bound
  have h_one_le : (1 : UInt64) ≤ x + align := by
    rw [UInt64.le_iff_toNat_le]; show 1 ≤ _; rw [h_xa]; omega
  have h_y : (x + align - 1).toNat = x.toNat + align.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ h_one_le, h_xa]; rfl
  have h_mod_le : (x + align - 1) % align ≤ (x + align - 1) := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
    exact Nat.mod_le _ _
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ h_mod_le,
      UInt64.toNat_mod, h_y]
  have h_mod_lt : (x.toNat + align.toNat - 1) % align.toNat < align.toNat :=
    Nat.mod_lt _ h_align_pos
  omega

-- ============================================================================
-- BSS InRange — `Exec.realizeSegment`'s zeroout bound, derived from
-- `Segment`'s gabi-07 witnesses (`fileszLeMemsz`, `addrBound`) plus
-- the alignment lemmas above.
-- ============================================================================

private theorem ea_ne_zero (s : Segment) : s.effectiveAlign ≠ 0 := by
  unfold Segment.effectiveAlign
  split
  · decide
  · intro h; rename_i hne; apply hne; simp [h]

private theorem ea_no_wrap (s : Segment) :
    s.vaddr.toNat + s.memsz.toNat + s.effectiveAlign.toNat < 2^64 := by
  have h_addr := s.addrBound
  have h_2_48 : (2:Nat)^48 + 1 < 2^64 := by decide
  unfold Segment.effectiveAlign
  split <;> rename_i h
  · have : s.align.toNat = 0 := by simp at h; rw [h]; rfl
    have h_one : (1 : UInt64).toNat = 1 := rfl
    rw [h_one]; omega
  · omega

/-- Writing `(memsz - filesz)` bytes at `(pageInset + filesz)` fits
    inside `pageLength`. Discharged from `Segment`'s gabi-07 witnesses
    via `alignUp_ge` / `alignDown_le`. Consumed by
    `Exec.realizeSegment` to skip the BSS-zero runtime check. -/
theorem bss_inRange (s : Segment) :
    Runtime.Region.InRange s.pageLength
      (s.pageInset + s.filesz) (s.memsz - s.filesz) := by
  have h_fm := s.fileszLeMemsz
  have h_addr := s.addrBound
  have h_ea_ne := ea_ne_zero s
  have h_pv_le_v : s.pageVaddr ≤ s.vaddr := alignDown_le _ _
  have h_pv_le_v_nat : s.pageVaddr.toNat ≤ s.vaddr.toNat :=
    UInt64.le_iff_toNat_le.mp h_pv_le_v
  have h_vm_no_wrap : s.vaddr.toNat + s.memsz.toNat < 2^64 := by
    have := ea_no_wrap s; omega
  have h_vm_eq : (s.vaddr + s.memsz).toNat = s.vaddr.toNat + s.memsz.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_vm_no_wrap
  have h_vmea : (s.vaddr + s.memsz).toNat + s.effectiveAlign.toNat < 2^64 := by
    rw [h_vm_eq]; exact ea_no_wrap s
  have h_au_ge : s.vaddr + s.memsz ≤ alignUp (s.vaddr + s.memsz) s.effectiveAlign :=
    alignUp_ge _ _ h_ea_ne h_vmea
  have h_au_ge_nat :
      s.vaddr.toNat + s.memsz.toNat ≤
        (alignUp (s.vaddr + s.memsz) s.effectiveAlign).toNat := by
    have := UInt64.le_iff_toNat_le.mp h_au_ge; rw [h_vm_eq] at this; exact this
  have h_au_le_pv :
      s.pageVaddr ≤ alignUp (s.vaddr + s.memsz) s.effectiveAlign := by
    apply UInt64.le_iff_toNat_le.mpr; omega
  have h_pl_nat : s.pageLength.toNat =
      (alignUp (s.vaddr + s.memsz) s.effectiveAlign).toNat - s.pageVaddr.toNat := by
    unfold Segment.pageLength
    rw [UInt64.toNat_sub_of_le _ _ h_au_le_pv]
  have h_pi_nat : s.pageInset.toNat = s.vaddr.toNat - s.pageVaddr.toNat := by
    unfold Segment.pageInset
    rw [UInt64.toNat_sub_of_le _ _ h_pv_le_v]
  have h_fm_nat : s.filesz.toNat ≤ s.memsz.toNat := UInt64.le_iff_toNat_le.mp h_fm
  have h_pif_no_wrap : s.pageInset.toNat + s.filesz.toNat < 2^64 := by
    rw [h_pi_nat]; omega
  have h_pif_nat : (s.pageInset + s.filesz).toNat = s.pageInset.toNat + s.filesz.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_pif_no_wrap
  have h_mf_nat : (s.memsz - s.filesz).toNat = s.memsz.toNat - s.filesz.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ h_fm]
  refine ⟨?_, ?_⟩
  · rw [UInt64.le_iff_toNat_le, h_pif_nat, h_pl_nat]; omega
  · have h_le1 : s.pageInset + s.filesz ≤ s.pageLength := by
      rw [UInt64.le_iff_toNat_le, h_pif_nat, h_pl_nat]; omega
    rw [UInt64.le_iff_toNat_le, h_mf_nat,
        UInt64.toNat_sub_of_le _ _ h_le1, h_pl_nat, h_pif_nat]
    omega

/-- Sorted segments ⇒ pairwise disjoint. With `endAddr[i] ≤ vaddr[j]`
    for `i < j`, every distinct pair satisfies `Segment.disjoint`. -/
theorem segmentsPairwiseDisjoint_of_segmentsSorted
    (lyt : ObjectLayout) (h : lyt.segmentsSorted) :
    lyt.segmentsPairwiseDisjoint := by
  intro i j hi hj hne
  rcases Nat.lt_or_ge i j with hlt | hge
  · exact Or.inl (h i hi j hj hlt)
  · have hgt : j < i := Nat.lt_of_le_of_ne hge (Ne.symm hne)
    exact Or.inr (h j hj i hi hgt)

/-- Bool ↔ Prop bridge for the runtime check.
    Trivial since `segmentsSortedB := decide segmentsSorted`. -/
theorem ObjectLayout.segmentsSortedB_iff_segmentsSorted (lyt : ObjectLayout) :
    lyt.segmentsSortedB = true ↔ lyt.segmentsSorted :=
  ⟨of_decide_eq_true, decide_eq_true⟩

/-- Every layout in `g.layouts`' success array has pairwise disjoint
    segments. Combines the per-layout `segmentsSorted` witness packed
    into the return subtype with `segmentsPairwiseDisjoint_of_segmentsSorted`. -/
theorem ObjectList.layouts_segmentsPairwiseDisjoint
    (g : ObjectList)
    {a : Array ObjectLayout}
    (h : a.size = g.val.size ∧ ∀ (i : Nat) (hi : i < a.size), a[i].segmentsSorted)
    (i : Nat) (hi : i < a.size) :
    a[i].segmentsPairwiseDisjoint :=
  segmentsPairwiseDisjoint_of_segmentsSorted _ (h.right i hi)

end LeanLoad.Thm

/-
Alignment helpers — pure UInt64 page math used throughout `Plan/`.
Base-free.

`alignDown x align` rounds `x` down to a multiple of `align`;
`alignUp x align` rounds up. `align = 0` is treated as alignment 1
(identity) so every page-arithmetic def below is total.

`effectiveAlign` lifts `align = 0` to `1` so internal proofs can
assume a positive alignment without adding a precondition.
-/

import LeanLoad.Parse.Address

namespace LeanLoad.Plan

-- ============================================================================
-- alignDown / alignUp
-- ============================================================================

/-- Round `x` down to a multiple of `align`. `align = 0` is treated
    as alignment 1 (identity). -/
def alignDown (x align : UInt64) : UInt64 :=
  if align == 0 then x else x - (x % align)

/-- Round `x` up to a multiple of `align`. `align = 0` is identity. -/
def alignUp (x align : UInt64) : UInt64 :=
  if align == 0 then x else alignDown (x + align - 1) align

#guard alignDown 0x1234 0x1000 == 0x1000
#guard alignUp 0x1234 0x1000 == 0x2000
#guard alignDown 0x1000 0x1000 == 0x1000
#guard alignUp   0x1000 0x1000 == 0x1000
#guard alignDown 0x1234 0 == 0x1234
#guard alignUp   0x1234 0 == 0x1234

/-- `alignDown` rounds toward zero. -/
theorem alignDown_le (x align : UInt64) : alignDown x align ≤ x := by
  unfold alignDown
  split
  · exact UInt64.le_refl _
  · have h_mod_le : x % align ≤ x := by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
      exact Nat.mod_le _ _
    exact UInt64.sub_le h_mod_le

theorem toNat_pos_of_ne_zero {a : UInt64} (h : a ≠ 0) : 0 < a.toNat := by
  rcases Nat.eq_zero_or_pos a.toNat with h0 | hp
  · exfalso; apply h; exact UInt64.toNat_inj.mp (h0.trans rfl.symm)
  · exact hp

/-- `alignUp x align ≤ x + align` (in `toNat`, no-wrap precondition). -/
theorem alignUp_le_add_align (x align : UInt64)
    (h_align_ne : align ≠ 0)
    (h_bound : x.toNat + align.toNat < 2^64) :
    (alignUp x align).toNat ≤ x.toNat + align.toNat := by
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
  rw [UInt64.toNat_sub_of_le _ _ h_mod_le, h_y]
  omega

/-- Closed-form `toNat` of `alignUp` (no-wrap precondition):
    `alignUp x ea ≡ (x + ea - 1) - ((x + ea - 1) % ea)`. -/
theorem alignUp_toNat (x align : UInt64)
    (h_align_ne : align ≠ 0)
    (h : x.toNat + align.toNat < 2 ^ 64) :
    (alignUp x align).toNat =
    (x.toNat + align.toNat - 1) -
    (x.toNat + align.toNat - 1) % align.toNat := by
  unfold alignUp alignDown
  rw [if_neg (by intro h0; exact h_align_ne (by simpa using h0))]
  rw [if_neg (by intro h0; exact h_align_ne (by simpa using h0))]
  have h_align_pos : 0 < align.toNat := toNat_pos_of_ne_zero h_align_ne
  have h_one_le : (1 : UInt64) ≤ x + align := by
    rw [UInt64.le_iff_toNat_le]; show 1 ≤ _
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]; omega
  have h_eq : (x + align - 1).toNat = x.toNat + align.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ h_one_le, UInt64.toNat_add, Nat.mod_eq_of_lt h]
    rfl
  have h_mod_le : (x + align - 1) % align ≤ (x + align - 1) := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]; exact Nat.mod_le _ _
  rw [UInt64.toNat_sub_of_le _ _ h_mod_le, UInt64.toNat_mod, h_eq]

/-- `alignUp` is monotone: `x ≤ y → alignUp x align ≤ alignUp y align`
    (in `toNat`, with the relevant no-wrap preconditions). -/
theorem alignUp_mono_toNat (x y align : UInt64)
    (h_align_ne : align ≠ 0)
    (h_x : x.toNat + align.toNat < 2 ^ 64)
    (h_y : y.toNat + align.toNat < 2 ^ 64)
    (h_xy : x.toNat ≤ y.toNat) :
    (alignUp x align).toNat ≤ (alignUp y align).toNat := by
  rw [alignUp_toNat _ _ h_align_ne h_x, alignUp_toNat _ _ h_align_ne h_y]
  -- Goal: (X - X % ea) ≤ (Y - Y % ea) where X = x.toNat + ea - 1, Y = y.toNat + ea - 1
  have h_xy_pre : x.toNat + align.toNat - 1 ≤ y.toNat + align.toNat - 1 := by omega
  have h_div_le : (x.toNat + align.toNat - 1) / align.toNat ≤
                  (y.toNat + align.toNat - 1) / align.toNat :=
    Nat.div_le_div_right h_xy_pre
  have h_x_eq : x.toNat + align.toNat - 1 -
      (x.toNat + align.toNat - 1) % align.toNat =
      ((x.toNat + align.toNat - 1) / align.toNat) * align.toNat := by
    have h1 := Nat.div_add_mod (x.toNat + align.toNat - 1) align.toNat
    have h2 : align.toNat * ((x.toNat + align.toNat - 1) / align.toNat) =
              ((x.toNat + align.toNat - 1) / align.toNat) * align.toNat :=
      Nat.mul_comm _ _
    omega
  have h_y_eq : y.toNat + align.toNat - 1 -
      (y.toNat + align.toNat - 1) % align.toNat =
      ((y.toNat + align.toNat - 1) / align.toNat) * align.toNat := by
    have h1 := Nat.div_add_mod (y.toNat + align.toNat - 1) align.toNat
    have h2 : align.toNat * ((y.toNat + align.toNat - 1) / align.toNat) =
              ((y.toNat + align.toNat - 1) / align.toNat) * align.toNat :=
      Nat.mul_comm _ _
    omega
  rw [h_x_eq, h_y_eq]
  exact Nat.mul_le_mul_right _ h_div_le

/-- Alignment-shift identity in `Nat`: when `d` is a multiple of `ea`
    and `0 < ea`, `d + alignUpNat x ea = alignUpNat (d + x) ea`,
    where `alignUpNat` is the closed-form `((. + ea - 1) / ea) * ea`. -/
private theorem alignUp_add_aligned_nat (d x ea : Nat) (h_pos : 0 < ea)
    (h_aligned : d % ea = 0) :
    d + ((x + ea - 1) / ea) * ea = ((d + x + ea - 1) / ea) * ea := by
  have h_d_eq : d = (d / ea) * ea := by
    have := Nat.div_add_mod d ea
    have h_comm : ea * (d / ea) = (d / ea) * ea := Nat.mul_comm _ _
    omega
  have h_split : d + x + ea - 1 = (x + ea - 1) + (d / ea) * ea := by
    have h_comm : (d / ea) * ea = ea * (d / ea) := Nat.mul_comm _ _
    omega
  rw [h_split, Nat.add_mul_div_right _ _ h_pos, Nat.add_mul]
  -- Goal: d + ((x + ea - 1) / ea) * ea = ((x + ea - 1) / ea) * ea + (d / ea) * ea
  -- = ((x + ea - 1) / ea) * ea + d (via h_d_eq.symm)
  omega

/-- `alignDown x ea + alignUp y ea = alignUp ((alignDown x ea) + y) ea`,
    in `toNat` (no-wrap precondition). The shift identity for the
    file-overlay bound: `alignDown vaddr ea` is aligned, so adding it
    pulls into the `alignUp`. -/
theorem alignDown_add_alignUp_toNat (x y align : UInt64)
    (h_align_ne : align ≠ 0)
    (h_y_no_wrap : y.toNat + align.toNat < 2 ^ 64)
    (h_sum_no_wrap : (alignDown x align).toNat + y.toNat + align.toNat < 2 ^ 64) :
    (alignDown x align).toNat + (alignUp y align).toNat =
    (alignUp ((alignDown x align) + y) align).toNat := by
  have h_align_pos : 0 < align.toNat := toNat_pos_of_ne_zero h_align_ne
  -- alignDown x align is aligned: (alignDown x align).toNat % ea = 0
  have h_aligned : (alignDown x align).toNat % align.toNat = 0 := by
    show (if align == 0 then x else x - x % align).toNat % align.toNat = 0
    rw [if_neg (by intro h; exact h_align_ne (by simpa using h))]
    have h_mod_le : x % align ≤ x := by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]; exact Nat.mod_le _ _
    rw [UInt64.toNat_sub_of_le _ _ h_mod_le, UInt64.toNat_mod]
    have h_eq : x.toNat - x.toNat % align.toNat =
                (x.toNat / align.toNat) * align.toNat := by
      have h1 := Nat.div_add_mod x.toNat align.toNat
      have h2 : align.toNat * (x.toNat / align.toNat) =
                (x.toNat / align.toNat) * align.toNat := Nat.mul_comm _ _
      omega
    rw [h_eq]
    exact Nat.mul_mod_left _ _
  -- (alignDown x align).toNat ≤ x.toNat
  have h_ad_le : (alignDown x align).toNat ≤ x.toNat :=
    UInt64.le_iff_toNat_le.mp (alignDown_le _ _)
  -- (alignDown x align + y).toNat = (alignDown x align).toNat + y.toNat (no wrap)
  have h_sum_lt : (alignDown x align).toNat + y.toNat < 2 ^ 64 := by omega
  have h_sum_eq : ((alignDown x align) + y).toNat =
                   (alignDown x align).toNat + y.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_sum_lt
  -- For alignUp ((alignDown x align) + y) align, need no-wrap precondition.
  have h_au_y_no_wrap : ((alignDown x align) + y).toNat + align.toNat < 2 ^ 64 := by
    rw [h_sum_eq]; omega
  rw [alignUp_toNat _ _ h_align_ne h_y_no_wrap]
  rw [alignUp_toNat _ _ h_align_ne h_au_y_no_wrap, h_sum_eq]
  -- Goal: ad.toNat + ((y.toNat + ea - 1) - (y.toNat + ea - 1) % ea) =
  --       ((ad.toNat + y.toNat + ea - 1) - (ad.toNat + y.toNat + ea - 1) % ea)
  -- where ad := alignDown x align
  -- Use the closed-form (a / ea) * ea via Nat.div_add_mod manipulation,
  -- then `alignUp_add_aligned_nat`.
  have h_a : (y.toNat + align.toNat - 1) -
             (y.toNat + align.toNat - 1) % align.toNat =
             ((y.toNat + align.toNat - 1) / align.toNat) * align.toNat := by
    have h1 := Nat.div_add_mod (y.toNat + align.toNat - 1) align.toNat
    have h2 : align.toNat * ((y.toNat + align.toNat - 1) / align.toNat) =
              ((y.toNat + align.toNat - 1) / align.toNat) * align.toNat :=
      Nat.mul_comm _ _
    omega
  have h_b : ((alignDown x align).toNat + y.toNat + align.toNat - 1) -
             ((alignDown x align).toNat + y.toNat + align.toNat - 1) % align.toNat =
             (((alignDown x align).toNat + y.toNat + align.toNat - 1) / align.toNat) *
             align.toNat := by
    have h1 := Nat.div_add_mod
      ((alignDown x align).toNat + y.toNat + align.toNat - 1) align.toNat
    have h2 : align.toNat *
        (((alignDown x align).toNat + y.toNat + align.toNat - 1) / align.toNat) =
        (((alignDown x align).toNat + y.toNat + align.toNat - 1) / align.toNat) *
        align.toNat := Nat.mul_comm _ _
    omega
  rw [h_a, h_b]
  exact alignUp_add_aligned_nat (alignDown x align).toNat y.toNat align.toNat
    h_align_pos h_aligned

/-- `alignUp` rounds away from zero. -/
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
-- effectiveAlign
-- ============================================================================

/-- Effective alignment: `align`, with `0` lifted to `1` so every
    page-arithmetic def is total. -/
def effectiveAlign (align : UInt64) : UInt64 :=
  LeanLoad.Parse.segmentLayoutAlign align

theorem effectiveAlign_ne_zero (align : UInt64) :
    effectiveAlign align ≠ 0 := by
  change (if align == 0 then (1 : UInt64) else align) ≠ 0
  split
  · decide
  · intro h; rename_i hne; apply hne; simp [h]

end LeanLoad.Plan

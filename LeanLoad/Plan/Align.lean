/-
Alignment helpers — pure UInt64 page math used throughout `Plan/`.
Base-free.

`alignDown x align` rounds `x` down to a multiple of `align`;
`alignUp x align` rounds up. `align = 0` is treated as alignment 1
(identity) so every page-arithmetic def below is total.

`effectiveAlign` lifts `align = 0` to `1` so internal proofs can
assume a positive alignment without adding a precondition.
-/

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

private theorem toNat_pos_of_ne_zero {a : UInt64} (h : a ≠ 0) : 0 < a.toNat := by
  rcases Nat.eq_zero_or_pos a.toNat with h0 | hp
  · exfalso; apply h; exact UInt64.toNat_inj.mp (h0.trans rfl.symm)
  · exact hp

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
  if align == 0 then 1 else align

theorem effectiveAlign_ne_zero (align : UInt64) :
    effectiveAlign align ≠ 0 := by
  unfold effectiveAlign
  split
  · decide
  · intro h; rename_i hne; apply hne; simp [h]

theorem ea_no_wrap (vaddr memsz align : UInt64)
    (h_addr : vaddr.toNat + memsz.toNat + align.toNat < 2 ^ 48) :
    vaddr.toNat + memsz.toNat + (effectiveAlign align).toNat < 2^64 := by
  have h_2_48 : (2:Nat)^48 + 1 < 2^64 := by decide
  unfold effectiveAlign
  split <;> rename_i h
  · have : align.toNat = 0 := by simp at h; rw [h]; rfl
    have h_one : (1 : UInt64).toNat = 1 := rfl
    rw [h_one]; omega
  · omega

end LeanLoad.Plan

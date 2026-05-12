/-
Base-aware plan: bundles a base-free `Plan.Plan` with the IO-supplied
`Reserve` and the coherence proof that ties them.

`BasedPlan` is the canonical input to `Materialize.build` and
`Materialize.ctorAddrs`. It replaces the ad-hoc `(plan, rsv, h_total)`
triple threaded through `Main.load` / `Main.debug` and centralises
the three separate `assignBases` invocations into one projection
(`bp.bases`) with closed-form lemmas.

Once `BasedPlan` exists, the materialize-stage safety witnesses
(`MmapsDisjoint`, `*Contained`) become provable structurally from
plan invariants. The bounds chain — `pageVaddr + fileOverlayLen ≤
pageEndAddr ≤ advance` (existing lemmas in `Plan/Layout.lean`) plus
`base + advance ≤ rsv.addr + rsv.len` (the workhorse
`base_plus_advance_le_rsv_end` below) — has every link as a named
lemma.
-/

import LeanLoad.Plan.Aggregate

namespace LeanLoad.Materialize

open LeanLoad
open LeanLoad.Plan (cumOffset cumOffset_succ_of_lt cumOffset_mono
                     assignBases assignBases_size assignBases_at_toNat)

/-- A pure-pipeline `Plan` plus the IO-supplied reservation it'll be
    materialized into, with the coherence proof threaded from
    `Reserve.run`'s subtype. Every materialize-stage consumer
    (`build`, `ctorAddrs`, `Main.realize`) takes a `BasedPlan` in
    place of `(plan, rsv, h_total)`. -/
structure BasedPlan where
  plan    : Plan.Plan
  rsv     : Reserve
  h_total : rsv.len = plan.load.totalSpan

namespace BasedPlan

/-- The number of loaded elves. Used as the `n` parameter on every
    `n`-indexed downstream type (`LoadOps n`, `SegmentOps n`, ...). -/
abbrev n (bp : BasedPlan) : Nat := bp.plan.objects.val.size

/-- Per-elf base addresses inside the reservation. `abbrev` so
    `bp.bases[i]` reduces to `assignBases bp.rsv.addr bp.plan.load`
    transparently in proofs. Hot consumers bind once via
    `let bases := bp.bases` to avoid re-materialising the array. -/
abbrev bases (bp : BasedPlan) : Array UInt64 :=
  assignBases bp.rsv.addr bp.plan.load

theorem bases_size (bp : BasedPlan) : bp.bases.size = bp.n :=
  (assignBases_size _ _).trans bp.plan.load.elfs_size

/-- `0 < bp.n` — the main executable is always present. -/
theorem n_pos (bp : BasedPlan) : 0 < bp.n :=
  bp.plan.objects.sizePos

theorem bases_size_pos (bp : BasedPlan) : 0 < bp.bases.size := by
  rw [bases_size]; exact bp.n_pos

/-- Global no-wrap: `rsv.addr + totalSpan` fits in UInt64. Falls out
    of `Reserve.noWrap` plus `h_total`. -/
theorem rsv_noWrap (bp : BasedPlan) :
    bp.rsv.addr.toNat + bp.plan.load.totalSpan.toNat < 2 ^ 64 := by
  rw [← bp.h_total]; exact bp.rsv.noWrap

/-- Closed-form for `bp.bases[i]`. -/
theorem bases_at_toNat (bp : BasedPlan) (i : Nat) (h : i < bp.n) :
    (bp.bases[i]'(by rw [bases_size]; exact h)).toNat =
    bp.rsv.addr.toNat + cumOffset bp.plan.load.elfs i := by
  have h_lp : i < bp.plan.load.elfs.size := by
    rw [bp.plan.load.elfs_size]; exact h
  exact assignBases_at_toNat bp.rsv.addr bp.plan.load bp.rsv_noWrap i h_lp

/-- Workhorse: the i-th elf's `[base, base + advance)` fits inside
    `[rsv.addr, rsv.addr + rsv.len)` in `Nat`. Every per-slot
    containment proof in `Materialize.LoadOps` chains through this. -/
theorem base_plus_advance_le_rsv_end (bp : BasedPlan)
    (i : Nat) (h : i < bp.n) :
    (bp.bases[i]'(by rw [bases_size]; exact h)).toNat +
    (bp.plan.load.elfs[i]'(by rw [bp.plan.load.elfs_size]; exact h)).advance.toNat ≤
    bp.rsv.addr.toNat + bp.rsv.len.toNat := by
  have h_lp : i < bp.plan.load.elfs.size := by
    rw [bp.plan.load.elfs_size]; exact h
  rw [bp.bases_at_toNat i h, bp.h_total, bp.plan.load.totalSpan_eq]
  have h_succ : cumOffset bp.plan.load.elfs i +
                (bp.plan.load.elfs[i]'h_lp).advance.toNat =
                cumOffset bp.plan.load.elfs (i + 1) :=
    (cumOffset_succ_of_lt _ h_lp).symm
  have h_mono : cumOffset bp.plan.load.elfs (i + 1) ≤
                cumOffset bp.plan.load.elfs bp.plan.load.elfs.size :=
    cumOffset_mono _ h_lp
  omega

/-- Each base sits below `rsv.addr + rsv.len`. Consequence of
    `bases_at_toNat` + `cumOffset_mono` + `totalSpan_eq`. -/
theorem bases_at_le_rsv_end (bp : BasedPlan) (i : Nat) (h : i < bp.n) :
    (bp.bases[i]'(by rw [bases_size]; exact h)).toNat ≤
    bp.rsv.addr.toNat + bp.rsv.len.toNat := by
  have h_lp : i < bp.plan.load.elfs.size := by
    rw [bp.plan.load.elfs_size]; exact h
  rw [bp.bases_at_toNat i h, bp.h_total, bp.plan.load.totalSpan_eq]
  have h_mono : cumOffset bp.plan.load.elfs i ≤
                cumOffset bp.plan.load.elfs bp.plan.load.elfs.size :=
    cumOffset_mono _ (Nat.le_of_lt h_lp)
  omega

/-- No-wrap of `bases[i] + delta` when `delta ≤ advance[i]`. The
    arithmetic precondition every UInt64 `(base + addr).toNat`
    decomposition needs. -/
theorem base_add_no_wrap (bp : BasedPlan) (i : Nat) (h : i < bp.n)
    (delta : UInt64)
    (h_delta : delta.toNat ≤
      (bp.plan.load.elfs[i]'(by rw [bp.plan.load.elfs_size]; exact h)).advance.toNat) :
    (bp.bases[i]'(by rw [bases_size]; exact h)).toNat + delta.toNat < 2 ^ 64 := by
  have h_bound := bp.base_plus_advance_le_rsv_end i h
  have h_no_wrap := bp.rsv.noWrap
  omega

/-- Across-elf base ordering: `bases[i₁] + advance[i₁] ≤ bases[i₂]`
    whenever `i₁ < i₂`. The cross-elf half of `MmapsDisjoint`. -/
theorem base_plus_advance_le_base (bp : BasedPlan)
    (i₁ i₂ : Nat) (h₁ : i₁ < bp.n) (h₂ : i₂ < bp.n) (h_lt : i₁ < i₂) :
    (bp.bases[i₁]'(by rw [bases_size]; exact h₁)).toNat +
    (bp.plan.load.elfs[i₁]'(by rw [bp.plan.load.elfs_size]; exact h₁)).advance.toNat ≤
    (bp.bases[i₂]'(by rw [bases_size]; exact h₂)).toNat := by
  have h_lp₁ : i₁ < bp.plan.load.elfs.size := by
    rw [bp.plan.load.elfs_size]; exact h₁
  rw [bp.bases_at_toNat i₁ h₁, bp.bases_at_toNat i₂ h₂]
  have h_succ : cumOffset bp.plan.load.elfs i₁ +
                (bp.plan.load.elfs[i₁]'h_lp₁).advance.toNat =
                cumOffset bp.plan.load.elfs (i₁ + 1) :=
    (cumOffset_succ_of_lt _ h_lp₁).symm
  have h_mono : cumOffset bp.plan.load.elfs (i₁ + 1) ≤
                cumOffset bp.plan.load.elfs i₂ :=
    cumOffset_mono _ h_lt
  omega

/-- The main executable's base — total since `bp.n > 0`. -/
def mainBase (bp : BasedPlan) : UInt64 :=
  bp.bases[0]'bp.bases_size_pos

end BasedPlan

end LeanLoad.Materialize

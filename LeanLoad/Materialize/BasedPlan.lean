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

-- ============================================================================
-- Per-segment slot bounds. Each of these turns a `(bp, i, j)` index
-- into an `InRange` fact about the slot `setupSlots` or `bakeReloc`
-- emits at that position. Used by the upcoming structural proof of
-- `Materialize.Safe`.
-- ============================================================================

/-- The `[base + sp.pageVaddr, base + sp.pageEndAddr)` page-aligned
    range is fully inside `[rsv.addr, rsv.addr + rsv.len)`. This is
    the parent bound — every per-slot bound below reduces to it. -/
theorem segment_pageRange_in_rsv (bp : BasedPlan)
    (i : Nat) (h_i : i < bp.n)
    (j : Nat) (h_j : j < (bp.plan.load.elfs[i]'(by
      rw [bp.plan.load.elfs_size]; exact h_i)).segments.size) :
    (bp.bases[i]'(by rw [bp.bases_size]; exact h_i)).toNat +
    ((bp.plan.load.elfs[i]'(by
      rw [bp.plan.load.elfs_size]; exact h_i)).segments[j]'h_j).pageVaddr.toNat +
    ((bp.plan.load.elfs[i]'(by
      rw [bp.plan.load.elfs_size]; exact h_i)).segments[j]'h_j).pageLength.toNat ≤
    bp.rsv.addr.toNat + bp.rsv.len.toNat := by
  have h_lp_i : i < bp.plan.load.elfs.size := by
    rw [bp.plan.load.elfs_size]; exact h_i
  let ep := bp.plan.load.elfs[i]'h_lp_i
  let sp := ep.segments[j]'h_j
  have h_pageEnd_pv : sp.pageVaddr.toNat + sp.pageLength.toNat =
      sp.pageEndAddr.toNat := by
    show _ = (sp.pageVaddr + sp.pageLength).toNat
    rw [UInt64.toNat_add]
    have h_no_wrap : sp.pageVaddr.toNat + sp.pageLength.toNat < 2 ^ 64 :=
      ep.pageEnd_lt j h_j
    exact (Nat.mod_eq_of_lt h_no_wrap).symm
  have h_pe_le_adv : sp.pageEndAddr.toNat ≤
      (bp.plan.load.elfs[i]'h_lp_i).advance.toNat :=
    ep.pageEndAddr_le_advance j h_j
  have h_base_advance := bp.base_plus_advance_le_rsv_end i h_i
  show (bp.bases[i]'(by rw [bp.bases_size]; exact h_i)).toNat +
       sp.pageVaddr.toNat + sp.pageLength.toNat ≤ _
  omega

/-- No-wrap of `base + pageVaddr + pageLength` — falls out of
    `segment_pageRange_in_rsv` plus `rsv.noWrap`. -/
theorem segment_pageRange_no_wrap (bp : BasedPlan)
    (i : Nat) (h_i : i < bp.n)
    (j : Nat) (h_j : j < (bp.plan.load.elfs[i]'(by
      rw [bp.plan.load.elfs_size]; exact h_i)).segments.size) :
    (bp.bases[i]'(by rw [bp.bases_size]; exact h_i)).toNat +
    ((bp.plan.load.elfs[i]'(by
      rw [bp.plan.load.elfs_size]; exact h_i)).segments[j]'h_j).pageVaddr.toNat +
    ((bp.plan.load.elfs[i]'(by
      rw [bp.plan.load.elfs_size]; exact h_i)).segments[j]'h_j).pageLength.toNat <
    2 ^ 64 := by
  have h_in_rsv := bp.segment_pageRange_in_rsv i h_i j h_j
  have h_rsv := bp.rsv.noWrap
  omega

/-- Helper: `(base + sp.pageVaddr).toNat = base.toNat + sp.pageVaddr.toNat`. -/
theorem segment_base_add_pageVaddr_toNat (bp : BasedPlan)
    (i : Nat) (h_i : i < bp.n)
    (j : Nat) (h_j : j < (bp.plan.load.elfs[i]'(by
      rw [bp.plan.load.elfs_size]; exact h_i)).segments.size) :
    ((bp.bases[i]'(by rw [bp.bases_size]; exact h_i)) +
      ((bp.plan.load.elfs[i]'(by
        rw [bp.plan.load.elfs_size]; exact h_i)).segments[j]'h_j).pageVaddr).toNat =
    (bp.bases[i]'(by rw [bp.bases_size]; exact h_i)).toNat +
    ((bp.plan.load.elfs[i]'(by
      rw [bp.plan.load.elfs_size]; exact h_i)).segments[j]'h_j).pageVaddr.toNat := by
  have h_no_wrap := bp.segment_pageRange_no_wrap i h_i j h_j
  rw [UInt64.toNat_add]
  refine Nat.mod_eq_of_lt ?_
  omega

/-- Lower bound: `rsv.addr ≤ base[i]`. Falls out of `bases_at_toNat`. -/
theorem rsv_addr_le_base (bp : BasedPlan) (i : Nat) (h_i : i < bp.n) :
    bp.rsv.addr.toNat ≤
    (bp.bases[i]'(by rw [bp.bases_size]; exact h_i)).toNat := by
  rw [bp.bases_at_toNat i h_i]
  have h_cum_nonneg : 0 ≤ Plan.cumOffset bp.plan.load.elfs i := Nat.zero_le _
  omega

/-- The mmap range `[base + sp.pageVaddr, base + sp.pageVaddr + sp.fileOverlayLen)`
    fits in the reservation. -/
theorem segment_mmapRange_in_rsv (bp : BasedPlan)
    (i : Nat) (h_i : i < bp.n)
    (j : Nat) (h_j : j < (bp.plan.load.elfs[i]'(by
      rw [bp.plan.load.elfs_size]; exact h_i)).segments.size) :
    Runtime.InRange
      ((bp.bases[i]'(by rw [bp.bases_size]; exact h_i)) +
        ((bp.plan.load.elfs[i]'(by
          rw [bp.plan.load.elfs_size]; exact h_i)).segments[j]'h_j).pageVaddr)
      ((bp.plan.load.elfs[i]'(by
        rw [bp.plan.load.elfs_size]; exact h_i)).segments[j]'h_j).fileOverlayLen
      bp.rsv.addr bp.rsv.len := by
  have h_pageEnd := bp.segment_pageRange_in_rsv i h_i j h_j
  have h_base_pv := bp.segment_base_add_pageVaddr_toNat i h_i j h_j
  have h_fo_le_pl := (bp.plan.load.elfs[i]'(by
    rw [bp.plan.load.elfs_size]; exact h_i)).fileOverlay_le_pageLength j h_j
  have h_lower := bp.rsv_addr_le_base i h_i
  refine ⟨?_, ?_⟩
  · rw [h_base_pv]; omega
  · rw [h_base_pv]; omega

/-- The mprotect range fits in the reservation. -/
theorem segment_mprotectRange_in_rsv (bp : BasedPlan)
    (i : Nat) (h_i : i < bp.n)
    (j : Nat) (h_j : j < (bp.plan.load.elfs[i]'(by
      rw [bp.plan.load.elfs_size]; exact h_i)).segments.size) :
    Runtime.InRange
      ((bp.bases[i]'(by rw [bp.bases_size]; exact h_i)) +
        ((bp.plan.load.elfs[i]'(by
          rw [bp.plan.load.elfs_size]; exact h_i)).segments[j]'h_j).pageVaddr)
      ((bp.plan.load.elfs[i]'(by
        rw [bp.plan.load.elfs_size]; exact h_i)).segments[j]'h_j).pageLength
      bp.rsv.addr bp.rsv.len := by
  have h_pageEnd := bp.segment_pageRange_in_rsv i h_i j h_j
  have h_base_pv := bp.segment_base_add_pageVaddr_toNat i h_i j h_j
  have h_lower := bp.rsv_addr_le_base i h_i
  refine ⟨?_, ?_⟩
  · rw [h_base_pv]; omega
  · rw [h_base_pv]; omega

/-- The zero range fits in the reservation. -/
theorem segment_zeroRange_in_rsv (bp : BasedPlan)
    (i : Nat) (h_i : i < bp.n)
    (j : Nat) (h_j : j < (bp.plan.load.elfs[i]'(by
      rw [bp.plan.load.elfs_size]; exact h_i)).segments.size) :
    Runtime.InRange
      ((bp.bases[i]'(by rw [bp.bases_size]; exact h_i)) +
        ((bp.plan.load.elfs[i]'(by
          rw [bp.plan.load.elfs_size]; exact h_i)).segments[j]'h_j).pageVaddr +
        ((bp.plan.load.elfs[i]'(by
          rw [bp.plan.load.elfs_size]; exact h_i)).segments[j]'h_j).pageInset +
        ((bp.plan.load.elfs[i]'(by
          rw [bp.plan.load.elfs_size]; exact h_i)).segments[j]'h_j).segment.filesz)
      ((bp.plan.load.elfs[i]'(by
        rw [bp.plan.load.elfs_size]; exact h_i)).segments[j]'h_j).partialBssLen
      bp.rsv.addr bp.rsv.len := by
  have h_pageEnd := bp.segment_pageRange_in_rsv i h_i j h_j
  have h_no_wrap := bp.segment_pageRange_no_wrap i h_i j h_j
  have h_base_pv := bp.segment_base_add_pageVaddr_toNat i h_i j h_j
  have h_lp_i : i < bp.plan.load.elfs.size := by
    rw [bp.plan.load.elfs_size]; exact h_i
  have h_lower := bp.rsv_addr_le_base i h_i
  have h_zero_end :
      ((bp.plan.load.elfs[i]'h_lp_i).segments[j]'h_j).pageInset.toNat +
      ((bp.plan.load.elfs[i]'h_lp_i).segments[j]'h_j).segment.filesz.toNat +
      ((bp.plan.load.elfs[i]'h_lp_i).segments[j]'h_j).partialBssLen.toNat ≤
      ((bp.plan.load.elfs[i]'h_lp_i).segments[j]'h_j).pageLength.toNat :=
    (bp.plan.load.elfs[i]'h_lp_i).zero_end_le_pageLength j h_j
  have h_vm_le := (bp.plan.load.elfs[i]'h_lp_i).vaddr_memsz_le_pageEnd j h_j
  have h_filesz_le_memsz := UInt64.le_iff_toNat_le.mp
    ((bp.plan.load.elfs[i]'h_lp_i).segments[j]'h_j).segment.fileszLeMemsz
  -- Step the address out: (base + pageVaddr + pageInset).toNat.
  have h_a1 :
      ((bp.bases[i]'(by rw [bp.bases_size]; exact h_i)) +
        ((bp.plan.load.elfs[i]'h_lp_i).segments[j]'h_j).pageVaddr).toNat +
      ((bp.plan.load.elfs[i]'h_lp_i).segments[j]'h_j).pageInset.toNat <
      2 ^ 64 := by
    rw [h_base_pv]; omega
  have h_a1_eq :
      ((bp.bases[i]'(by rw [bp.bases_size]; exact h_i)) +
        ((bp.plan.load.elfs[i]'h_lp_i).segments[j]'h_j).pageVaddr +
        ((bp.plan.load.elfs[i]'h_lp_i).segments[j]'h_j).pageInset).toNat =
      ((bp.bases[i]'(by rw [bp.bases_size]; exact h_i)) +
        ((bp.plan.load.elfs[i]'h_lp_i).segments[j]'h_j).pageVaddr).toNat +
      ((bp.plan.load.elfs[i]'h_lp_i).segments[j]'h_j).pageInset.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_a1
  have h_a2 :
      ((bp.bases[i]'(by rw [bp.bases_size]; exact h_i)) +
        ((bp.plan.load.elfs[i]'h_lp_i).segments[j]'h_j).pageVaddr +
        ((bp.plan.load.elfs[i]'h_lp_i).segments[j]'h_j).pageInset).toNat +
      ((bp.plan.load.elfs[i]'h_lp_i).segments[j]'h_j).segment.filesz.toNat <
      2 ^ 64 := by
    rw [h_a1_eq, h_base_pv]; omega
  have h_a2_eq :
      ((bp.bases[i]'(by rw [bp.bases_size]; exact h_i)) +
        ((bp.plan.load.elfs[i]'h_lp_i).segments[j]'h_j).pageVaddr +
        ((bp.plan.load.elfs[i]'h_lp_i).segments[j]'h_j).pageInset +
        ((bp.plan.load.elfs[i]'h_lp_i).segments[j]'h_j).segment.filesz).toNat =
      ((bp.bases[i]'(by rw [bp.bases_size]; exact h_i)) +
        ((bp.plan.load.elfs[i]'h_lp_i).segments[j]'h_j).pageVaddr +
        ((bp.plan.load.elfs[i]'h_lp_i).segments[j]'h_j).pageInset).toNat +
      ((bp.plan.load.elfs[i]'h_lp_i).segments[j]'h_j).segment.filesz.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_a2
  refine ⟨?_, ?_⟩
  · rw [h_a2_eq, h_a1_eq, h_base_pv]; omega
  · rw [h_a2_eq, h_a1_eq, h_base_pv]; omega

-- ============================================================================
-- Disjointness lemmas. Two flavours:
--   • within-elf — same `i`, distinct segments `j₁ < j₂`. Pulls
--     `Plan.Sorted` (page-aligned non-overlap from ElfPlan) into a
--     `Runtime.Disjoint` claim about the mmap'd ranges.
--   • cross-elf  — distinct elves `i₁ < i₂`. Uses the existing
--     `base_plus_advance_le_base` for the dominant inequality.
--
-- Both end at the same shape: `Disjoint (base + sp.pageVaddr)
-- (fileOverlayLen or pageLength) (base' + sp'.pageVaddr) (...)`.
-- ============================================================================

/-- Within an elf: page-aligned segment ranges don't overlap. Lifts
    `Plan.Sorted` (the existing ElfPlan invariant) from `pageEndAddr ≤
    pageVaddr` to `base + pageEnd ≤ base + pageVaddr'`. -/
theorem within_elf_pageRange_disjoint (bp : BasedPlan)
    (i : Nat) (h_i : i < bp.n)
    (j₁ j₂ : Nat)
    (h_j₁ : j₁ < (bp.plan.load.elfs[i]'(by
      rw [bp.plan.load.elfs_size]; exact h_i)).segments.size)
    (h_j₂ : j₂ < (bp.plan.load.elfs[i]'(by
      rw [bp.plan.load.elfs_size]; exact h_i)).segments.size)
    (h_lt : j₁ < j₂) :
    Runtime.Disjoint
      ((bp.bases[i]'(by rw [bp.bases_size]; exact h_i)) +
        ((bp.plan.load.elfs[i]'(by
          rw [bp.plan.load.elfs_size]; exact h_i)).segments[j₁]'h_j₁).pageVaddr)
      ((bp.plan.load.elfs[i]'(by
        rw [bp.plan.load.elfs_size]; exact h_i)).segments[j₁]'h_j₁).pageLength
      ((bp.bases[i]'(by rw [bp.bases_size]; exact h_i)) +
        ((bp.plan.load.elfs[i]'(by
          rw [bp.plan.load.elfs_size]; exact h_i)).segments[j₂]'h_j₂).pageVaddr)
      ((bp.plan.load.elfs[i]'(by
        rw [bp.plan.load.elfs_size]; exact h_i)).segments[j₂]'h_j₂).pageLength := by
  have h_lp_i : i < bp.plan.load.elfs.size := by
    rw [bp.plan.load.elfs_size]; exact h_i
  -- The page-aligned ranges are sorted by `ElfPlan.segmentsSorted`:
  -- `sp_j1.pageEndAddr ≤ sp_j2.pageVaddr`. Lift to Nat.
  have h_pe_le_pv :
      ((bp.plan.load.elfs[i]'h_lp_i).segments[j₁]'h_j₁).pageEndAddr ≤
      ((bp.plan.load.elfs[i]'h_lp_i).segments[j₂]'h_j₂).pageVaddr :=
    (bp.plan.load.elfs[i]'h_lp_i).segmentsSorted j₁ h_j₁ j₂ h_j₂ h_lt
  have h_pe_le_pv_nat :
      ((bp.plan.load.elfs[i]'h_lp_i).segments[j₁]'h_j₁).pageEndAddr.toNat ≤
      ((bp.plan.load.elfs[i]'h_lp_i).segments[j₂]'h_j₂).pageVaddr.toNat :=
    UInt64.le_iff_toNat_le.mp h_pe_le_pv
  -- `pageEndAddr.toNat = pageVaddr.toNat + pageLength.toNat` via `pageEnd_lt`.
  have h_no_wrap_j₁ :
      ((bp.plan.load.elfs[i]'h_lp_i).segments[j₁]'h_j₁).pageVaddr.toNat +
      ((bp.plan.load.elfs[i]'h_lp_i).segments[j₁]'h_j₁).pageLength.toNat <
      2 ^ 64 :=
    (bp.plan.load.elfs[i]'h_lp_i).pageEnd_lt j₁ h_j₁
  have h_pe_eq :
      ((bp.plan.load.elfs[i]'h_lp_i).segments[j₁]'h_j₁).pageEndAddr.toNat =
      ((bp.plan.load.elfs[i]'h_lp_i).segments[j₁]'h_j₁).pageVaddr.toNat +
      ((bp.plan.load.elfs[i]'h_lp_i).segments[j₁]'h_j₁).pageLength.toNat := by
    change ((_ + _ : UInt64)).toNat = _
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_no_wrap_j₁
  have h_base_pv₁ := bp.segment_base_add_pageVaddr_toNat i h_i j₁ h_j₁
  have h_base_pv₂ := bp.segment_base_add_pageVaddr_toNat i h_i j₂ h_j₂
  have h_no_wrap_base₁ := bp.segment_pageRange_no_wrap i h_i j₁ h_j₁
  -- Disjoint is `LHS_end ≤ RHS_start ∨ RHS_end ≤ LHS_start`. Take left,
  -- normalise both `(base + pageVaddr).toNat` decompositions, then
  -- `omega`.
  left
  show ((bp.bases[i]'(by rw [bp.bases_size]; exact h_i)) +
        ((bp.plan.load.elfs[i]'h_lp_i).segments[j₁]'h_j₁).pageVaddr).toNat +
       ((bp.plan.load.elfs[i]'h_lp_i).segments[j₁]'h_j₁).pageLength.toNat ≤
       ((bp.bases[i]'(by rw [bp.bases_size]; exact h_i)) +
        ((bp.plan.load.elfs[i]'h_lp_i).segments[j₂]'h_j₂).pageVaddr).toNat
  rw [h_base_pv₁, h_base_pv₂]
  omega

/-- Within an elf: mmap ranges don't overlap. Same proof skeleton as
    `within_elf_pageRange_disjoint` but with `fileOverlayLen ≤ pageLength`
    shrinkage applied to both sides. -/
theorem within_elf_mmapRange_disjoint (bp : BasedPlan)
    (i : Nat) (h_i : i < bp.n)
    (j₁ j₂ : Nat)
    (h_j₁ : j₁ < (bp.plan.load.elfs[i]'(by
      rw [bp.plan.load.elfs_size]; exact h_i)).segments.size)
    (h_j₂ : j₂ < (bp.plan.load.elfs[i]'(by
      rw [bp.plan.load.elfs_size]; exact h_i)).segments.size)
    (h_lt : j₁ < j₂) :
    Runtime.Disjoint
      ((bp.bases[i]'(by rw [bp.bases_size]; exact h_i)) +
        ((bp.plan.load.elfs[i]'(by
          rw [bp.plan.load.elfs_size]; exact h_i)).segments[j₁]'h_j₁).pageVaddr)
      ((bp.plan.load.elfs[i]'(by
        rw [bp.plan.load.elfs_size]; exact h_i)).segments[j₁]'h_j₁).fileOverlayLen
      ((bp.bases[i]'(by rw [bp.bases_size]; exact h_i)) +
        ((bp.plan.load.elfs[i]'(by
          rw [bp.plan.load.elfs_size]; exact h_i)).segments[j₂]'h_j₂).pageVaddr)
      ((bp.plan.load.elfs[i]'(by
        rw [bp.plan.load.elfs_size]; exact h_i)).segments[j₂]'h_j₂).fileOverlayLen := by
  have h_page := bp.within_elf_pageRange_disjoint i h_i j₁ j₂ h_j₁ h_j₂ h_lt
  have h_lp_i : i < bp.plan.load.elfs.size := by
    rw [bp.plan.load.elfs_size]; exact h_i
  have h_fo_le_pl₁ :=
    (bp.plan.load.elfs[i]'h_lp_i).fileOverlay_le_pageLength j₁ h_j₁
  have h_fo_le_pl₂ :=
    (bp.plan.load.elfs[i]'h_lp_i).fileOverlay_le_pageLength j₂ h_j₂
  -- `h_page : Disjoint base+pv₁ pageLength₁ base+pv₂ pageLength₂` —
  -- shrink each len from pageLength to fileOverlayLen.
  rcases h_page with h_left | h_right
  · left; omega
  · right; omega

/-- Cross-elf: page ranges of any two distinct elves don't overlap.
    Uses `base_plus_advance_le_base` plus `pageEndAddr_le_advance` to
    place the entire page range inside the per-elf slice. -/
theorem cross_elf_pageRange_disjoint (bp : BasedPlan)
    (i₁ i₂ : Nat) (h_i₁ : i₁ < bp.n) (h_i₂ : i₂ < bp.n)
    (j₁ : Nat) (h_j₁ : j₁ < (bp.plan.load.elfs[i₁]'(by
      rw [bp.plan.load.elfs_size]; exact h_i₁)).segments.size)
    (j₂ : Nat) (h_j₂ : j₂ < (bp.plan.load.elfs[i₂]'(by
      rw [bp.plan.load.elfs_size]; exact h_i₂)).segments.size)
    (h_lt : i₁ < i₂) :
    Runtime.Disjoint
      ((bp.bases[i₁]'(by rw [bp.bases_size]; exact h_i₁)) +
        ((bp.plan.load.elfs[i₁]'(by
          rw [bp.plan.load.elfs_size]; exact h_i₁)).segments[j₁]'h_j₁).pageVaddr)
      ((bp.plan.load.elfs[i₁]'(by
        rw [bp.plan.load.elfs_size]; exact h_i₁)).segments[j₁]'h_j₁).pageLength
      ((bp.bases[i₂]'(by rw [bp.bases_size]; exact h_i₂)) +
        ((bp.plan.load.elfs[i₂]'(by
          rw [bp.plan.load.elfs_size]; exact h_i₂)).segments[j₂]'h_j₂).pageVaddr)
      ((bp.plan.load.elfs[i₂]'(by
        rw [bp.plan.load.elfs_size]; exact h_i₂)).segments[j₂]'h_j₂).pageLength := by
  have h_base_pv₁ := bp.segment_base_add_pageVaddr_toNat i₁ h_i₁ j₁ h_j₁
  have h_pageEnd₁ := bp.segment_pageRange_in_rsv i₁ h_i₁ j₁ h_j₁
  have h_pageEnd₂ := bp.segment_pageRange_in_rsv i₂ h_i₂ j₂ h_j₂
  have h_no_wrap₁ := bp.segment_pageRange_no_wrap i₁ h_i₁ j₁ h_j₁
  have h_no_wrap₂ := bp.segment_pageRange_no_wrap i₂ h_i₂ j₂ h_j₂
  have h_lp_i₁ : i₁ < bp.plan.load.elfs.size := by
    rw [bp.plan.load.elfs_size]; exact h_i₁
  have h_lp_i₂ : i₂ < bp.plan.load.elfs.size := by
    rw [bp.plan.load.elfs_size]; exact h_i₂
  have h_pe₁ : ((bp.plan.load.elfs[i₁]'h_lp_i₁).segments[j₁]'h_j₁).pageVaddr.toNat +
               ((bp.plan.load.elfs[i₁]'h_lp_i₁).segments[j₁]'h_j₁).pageLength.toNat ≤
               (bp.plan.load.elfs[i₁]'h_lp_i₁).advance.toNat := by
    have h_eq : ((bp.plan.load.elfs[i₁]'h_lp_i₁).segments[j₁]'h_j₁).pageVaddr.toNat +
                ((bp.plan.load.elfs[i₁]'h_lp_i₁).segments[j₁]'h_j₁).pageLength.toNat =
                ((bp.plan.load.elfs[i₁]'h_lp_i₁).segments[j₁]'h_j₁).pageEndAddr.toNat := by
      show _ =
        (((bp.plan.load.elfs[i₁]'h_lp_i₁).segments[j₁]'h_j₁).pageVaddr +
         ((bp.plan.load.elfs[i₁]'h_lp_i₁).segments[j₁]'h_j₁).pageLength).toNat
      rw [UInt64.toNat_add]
      have h_no_wrap :=
        (bp.plan.load.elfs[i₁]'h_lp_i₁).pageEnd_lt j₁ h_j₁
      exact (Nat.mod_eq_of_lt h_no_wrap).symm
    rw [h_eq]
    exact (bp.plan.load.elfs[i₁]'h_lp_i₁).pageEndAddr_le_advance j₁ h_j₁
  have h_b_le_b := bp.base_plus_advance_le_base i₁ i₂ h_i₁ h_i₂ h_lt
  have h_base_pv₂ := bp.segment_base_add_pageVaddr_toNat i₂ h_i₂ j₂ h_j₂
  -- Take left disjunct, normalise both `(base + pv).toNat`, omega.
  left
  show ((bp.bases[i₁]'(by rw [bp.bases_size]; exact h_i₁)) +
        ((bp.plan.load.elfs[i₁]'h_lp_i₁).segments[j₁]'h_j₁).pageVaddr).toNat +
       ((bp.plan.load.elfs[i₁]'h_lp_i₁).segments[j₁]'h_j₁).pageLength.toNat ≤
       ((bp.bases[i₂]'(by rw [bp.bases_size]; exact h_i₂)) +
        ((bp.plan.load.elfs[i₂]'h_lp_i₂).segments[j₂]'h_j₂).pageVaddr).toNat
  rw [h_base_pv₁, h_base_pv₂]
  omega

/-- Cross-elf mmap-range disjointness — shrink page-range disjointness
    using `fileOverlay_le_pageLength`. -/
theorem cross_elf_mmapRange_disjoint (bp : BasedPlan)
    (i₁ i₂ : Nat) (h_i₁ : i₁ < bp.n) (h_i₂ : i₂ < bp.n)
    (j₁ : Nat) (h_j₁ : j₁ < (bp.plan.load.elfs[i₁]'(by
      rw [bp.plan.load.elfs_size]; exact h_i₁)).segments.size)
    (j₂ : Nat) (h_j₂ : j₂ < (bp.plan.load.elfs[i₂]'(by
      rw [bp.plan.load.elfs_size]; exact h_i₂)).segments.size)
    (h_lt : i₁ < i₂) :
    Runtime.Disjoint
      ((bp.bases[i₁]'(by rw [bp.bases_size]; exact h_i₁)) +
        ((bp.plan.load.elfs[i₁]'(by
          rw [bp.plan.load.elfs_size]; exact h_i₁)).segments[j₁]'h_j₁).pageVaddr)
      ((bp.plan.load.elfs[i₁]'(by
        rw [bp.plan.load.elfs_size]; exact h_i₁)).segments[j₁]'h_j₁).fileOverlayLen
      ((bp.bases[i₂]'(by rw [bp.bases_size]; exact h_i₂)) +
        ((bp.plan.load.elfs[i₂]'(by
          rw [bp.plan.load.elfs_size]; exact h_i₂)).segments[j₂]'h_j₂).pageVaddr)
      ((bp.plan.load.elfs[i₂]'(by
        rw [bp.plan.load.elfs_size]; exact h_i₂)).segments[j₂]'h_j₂).fileOverlayLen := by
  have h_page := bp.cross_elf_pageRange_disjoint i₁ i₂ h_i₁ h_i₂ j₁ h_j₁ j₂ h_j₂ h_lt
  have h_lp_i₁ : i₁ < bp.plan.load.elfs.size := by
    rw [bp.plan.load.elfs_size]; exact h_i₁
  have h_lp_i₂ : i₂ < bp.plan.load.elfs.size := by
    rw [bp.plan.load.elfs_size]; exact h_i₂
  have h_fo_le_pl₁ :=
    (bp.plan.load.elfs[i₁]'h_lp_i₁).fileOverlay_le_pageLength j₁ h_j₁
  have h_fo_le_pl₂ :=
    (bp.plan.load.elfs[i₂]'h_lp_i₂).fileOverlay_le_pageLength j₂ h_j₂
  rcases h_page with h_left | h_right
  · left; omega
  · right; omega

/-- The store range `[base + r_offset, base + r_offset + size)` fits
    in the reservation for any `RelocEntry` with the `coversRela`
    witness on its parent segment. The 4-or-8-byte width is bounded
    by `coversRela`'s conservative 8-byte window. -/
theorem segment_storeRange_in_rsv (bp : BasedPlan)
    (i : Nat) (h_i : i < bp.n)
    (j : Nat) (h_j : j < (bp.plan.load.elfs[i]'(by
      rw [bp.plan.load.elfs_size]; exact h_i)).segments.size)
    (r_offset : UInt64)
    (h_cov : Elaborate.coversRela
      ((bp.plan.load.elfs[i]'(by
        rw [bp.plan.load.elfs_size]; exact h_i)).segments[j]'h_j).segment.vaddr
      ((bp.plan.load.elfs[i]'(by
        rw [bp.plan.load.elfs_size]; exact h_i)).segments[j]'h_j).segment.memsz
      r_offset)
    (size : UInt64) (h_size : size.toNat ≤ 8) :
    Runtime.InRange
      ((bp.bases[i]'(by rw [bp.bases_size]; exact h_i)) + r_offset)
      size bp.rsv.addr bp.rsv.len := by
  have h_pageEnd := bp.segment_pageRange_in_rsv i h_i j h_j
  have h_no_wrap := bp.segment_pageRange_no_wrap i h_i j h_j
  have h_lp_i : i < bp.plan.load.elfs.size := by
    rw [bp.plan.load.elfs_size]; exact h_i
  have h_vm_le := (bp.plan.load.elfs[i]'h_lp_i).vaddr_memsz_le_pageEnd j h_j
  obtain ⟨h_vaddr_le, h_ro8_le_vm⟩ := h_cov
  have h_ro_no_wrap :
      (bp.bases[i]'(by rw [bp.bases_size]; exact h_i)).toNat +
      r_offset.toNat < 2 ^ 64 := by omega
  have h_base_ro_eq :
      ((bp.bases[i]'(by rw [bp.bases_size]; exact h_i)) + r_offset).toNat =
      (bp.bases[i]'(by rw [bp.bases_size]; exact h_i)).toNat + r_offset.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_ro_no_wrap
  have h_lower := bp.rsv_addr_le_base i h_i
  refine ⟨?_, ?_⟩
  · rw [h_base_ro_eq]; omega
  · rw [h_base_ro_eq]; omega

end BasedPlan

end LeanLoad.Materialize

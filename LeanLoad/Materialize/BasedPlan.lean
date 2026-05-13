/-
Base-aware plan: bundles a base-free `Plan.Plan` with the IO-supplied
`Reserve` and the coherence proof that ties them.

`BasedPlan` is the canonical input to `Materialize.build` and
`Materialize.ctorAddrs`. It replaces the ad-hoc `(plan, rsv, h_total)`
triple threaded through `Main.load` / `Main.debug` and centralises
the three separate `assignBases` invocations into one projection
(`bp.bases`) with closed-form lemmas.

Once `BasedPlan` exists, the materialize-stage safety witness
`LoadSafe` (and its `ElfSafe` / `SegmentSafe` constituents) becomes
provable structurally from plan invariants. The bounds chain —
`pageVaddr + fileOverlayLen ≤ pageEndAddr ≤ advance` (existing
lemmas in `Plan/Layout.lean`) plus `base + advance ≤ rsv.addr +
rsv.len` (the workhorse `base_plus_advance_le_rsv_end` below) —
has every link as a named lemma.
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
  h_total : rsv.len = plan.layout.totalSpan

namespace BasedPlan

/-- The number of loaded elves. Used as the `n` parameter on every
    `n`-indexed downstream type (`LoadOps n`, `SegmentOps n`, ...). -/
abbrev n (bp : BasedPlan) : Nat := bp.plan.objects.val.size

/-- Per-elf base addresses inside the reservation. `abbrev` so
    `bp.bases[i]` reduces to `assignBases bp.rsv.addr bp.plan.layout`
    transparently in proofs. Hot consumers bind once via
    `let bases := bp.bases` to avoid re-materialising the array. -/
abbrev bases (bp : BasedPlan) : Array UInt64 :=
  assignBases bp.rsv.addr bp.plan.layout

theorem bases_size (bp : BasedPlan) : bp.bases.size = bp.n :=
  (assignBases_size _ _).trans bp.plan.layout.elfs_size

/-- `0 < bp.n` — the main executable is always present. -/
theorem n_pos (bp : BasedPlan) : 0 < bp.n :=
  bp.plan.objects.sizePos

theorem bases_size_pos (bp : BasedPlan) : 0 < bp.bases.size := by
  rw [bases_size]; exact bp.n_pos

/-- Global no-wrap: `rsv.addr + totalSpan` fits in UInt64. Falls out
    of `Reserve.noWrap` plus `h_total`. -/
theorem rsv_noWrap (bp : BasedPlan) :
    bp.rsv.addr.toNat + bp.plan.layout.totalSpan.toNat < 2 ^ 64 := by
  rw [← bp.h_total]; exact bp.rsv.noWrap

-- ============================================================================
-- Fin-indexed accessors. Bundles the size proof on the value (via
-- `Fin n.isLt`) so call sites don't have to thread `(by rw [bp.bases_size];
-- exact h_i)`-style ritual everywhere. All `abbrev` so the underlying
-- array indexing form is recovered for unification when needed.
-- ============================================================================

/-- `i`-th elf plan, indexed totally by `Fin bp.n`. -/
abbrev elfAt (bp : BasedPlan) (i : Fin bp.n) : Plan.ElfLayout bp.n :=
  bp.plan.layout.elfs[i.val]'(by rw [bp.plan.layout.elfs_size]; exact i.isLt)

/-- `i`-th elf's base address. -/
abbrev baseAt (bp : BasedPlan) (i : Fin bp.n) : UInt64 :=
  bp.bases[i.val]'(by rw [bp.bases_size]; exact i.isLt)

/-- `i`-th elf's open file handle (held until process exit). -/
abbrev handleAt (bp : BasedPlan) (i : Fin bp.n) : Runtime.FileHandle :=
  (bp.plan.objects.val[i.val]'i.isLt).handle

/-- `(i, j)`-th segment plan. -/
abbrev segAt (bp : BasedPlan) (i : Fin bp.n)
    (j : Fin (bp.elfAt i).segments.size) : Plan.SegmentLayout bp.n :=
  (bp.elfAt i).segments[j]

/-- Closed-form for `bp.baseAt i`. -/
theorem baseAt_toNat (bp : BasedPlan) (i : Fin bp.n) :
    (bp.baseAt i).toNat =
    bp.rsv.addr.toNat + cumOffset bp.plan.layout.elfs i.val := by
  have h_lp : i.val < bp.plan.layout.elfs.size := by
    rw [bp.plan.layout.elfs_size]; exact i.isLt
  exact assignBases_at_toNat bp.rsv.addr bp.plan.layout bp.rsv_noWrap i.val h_lp

/-- Workhorse: the i-th elf's `[base, base + advance)` fits inside
    `[rsv.addr, rsv.addr + rsv.len)` in `Nat`. Every per-slot
    containment proof in `Materialize.LoadOps` chains through this. -/
theorem base_plus_advance_le_rsv_end (bp : BasedPlan) (i : Fin bp.n) :
    (bp.baseAt i).toNat + (bp.elfAt i).advance.toNat ≤
    bp.rsv.addr.toNat + bp.rsv.len.toNat := by
  have h_lp : i.val < bp.plan.layout.elfs.size := by
    rw [bp.plan.layout.elfs_size]; exact i.isLt
  show (bp.baseAt i).toNat +
       (bp.plan.layout.elfs[i.val]'h_lp).advance.toNat ≤ _
  rw [bp.baseAt_toNat i, bp.h_total, bp.plan.layout.totalSpan_eq]
  have h_succ : cumOffset bp.plan.layout.elfs i.val +
                (bp.plan.layout.elfs[i.val]'h_lp).advance.toNat =
                cumOffset bp.plan.layout.elfs (i.val + 1) :=
    (cumOffset_succ_of_lt _ h_lp).symm
  have h_mono : cumOffset bp.plan.layout.elfs (i.val + 1) ≤
                cumOffset bp.plan.layout.elfs bp.plan.layout.elfs.size :=
    cumOffset_mono _ h_lp
  omega

/-- Each base sits below `rsv.addr + rsv.len`. Consequence of
    `baseAt_toNat` + `cumOffset_mono` + `totalSpan_eq`. -/
theorem baseAt_le_rsv_end (bp : BasedPlan) (i : Fin bp.n) :
    (bp.baseAt i).toNat ≤ bp.rsv.addr.toNat + bp.rsv.len.toNat := by
  have h_lp : i.val < bp.plan.layout.elfs.size := by
    rw [bp.plan.layout.elfs_size]; exact i.isLt
  rw [bp.baseAt_toNat i, bp.h_total, bp.plan.layout.totalSpan_eq]
  have h_mono : cumOffset bp.plan.layout.elfs i.val ≤
                cumOffset bp.plan.layout.elfs bp.plan.layout.elfs.size :=
    cumOffset_mono _ (Nat.le_of_lt h_lp)
  omega

/-- No-wrap of `baseAt i + delta` when `delta ≤ advance`. The
    arithmetic precondition every UInt64 `(base + addr).toNat`
    decomposition needs. -/
theorem base_add_no_wrap (bp : BasedPlan) (i : Fin bp.n) (delta : UInt64)
    (h_delta : delta.toNat ≤ (bp.elfAt i).advance.toNat) :
    (bp.baseAt i).toNat + delta.toNat < 2 ^ 64 := by
  have h_bound := bp.base_plus_advance_le_rsv_end i
  have h_no_wrap := bp.rsv.noWrap
  omega

/-- Across-elf base ordering: `bases[i₁] + advance[i₁] ≤ bases[i₂]`
    whenever `i₁ < i₂`. The cross-elf half of `MmapsDisjoint`. -/
theorem base_plus_advance_le_base (bp : BasedPlan) (i₁ i₂ : Fin bp.n)
    (h_lt : i₁ < i₂) :
    (bp.baseAt i₁).toNat + (bp.elfAt i₁).advance.toNat ≤
    (bp.baseAt i₂).toNat := by
  have h_lp₁ : i₁.val < bp.plan.layout.elfs.size := by
    rw [bp.plan.layout.elfs_size]; exact i₁.isLt
  show (bp.baseAt i₁).toNat +
       (bp.plan.layout.elfs[i₁.val]'h_lp₁).advance.toNat ≤ _
  rw [bp.baseAt_toNat i₁, bp.baseAt_toNat i₂]
  have h_succ : cumOffset bp.plan.layout.elfs i₁.val +
                (bp.plan.layout.elfs[i₁.val]'h_lp₁).advance.toNat =
                cumOffset bp.plan.layout.elfs (i₁.val + 1) :=
    (cumOffset_succ_of_lt _ h_lp₁).symm
  have h_mono : cumOffset bp.plan.layout.elfs (i₁.val + 1) ≤
                cumOffset bp.plan.layout.elfs i₂.val :=
    cumOffset_mono _ h_lt
  omega

/-- The main executable's base — total since `bp.n > 0`. -/
def mainBase (bp : BasedPlan) : UInt64 :=
  bp.bases[0]'bp.bases_size_pos

-- ============================================================================
-- Per-segment slot bounds. Each of these turns a `(bp, i, j)` index
-- into an `InRange` fact about the slot `setupSlots` or `bakeReloc`
-- emits at that position. Consumed by `Materialize.Build` to assemble
-- `SegmentSafe` witnesses in lock-step with `SegmentOps`.
-- ============================================================================

/-- The `[base + sp.pageVaddr, base + sp.pageEndAddr)` page-aligned
    range is fully inside `[rsv.addr, rsv.addr + rsv.len)`. This is
    the parent bound — every per-slot bound below reduces to it. -/
theorem segment_pageRange_in_rsv (bp : BasedPlan) (i : Fin bp.n)
    (j : Fin (bp.elfAt i).segments.size) :
    (bp.baseAt i).toNat + (bp.segAt i j).pageVaddr.toNat +
      (bp.segAt i j).pageLength.toNat ≤
    bp.rsv.addr.toNat + bp.rsv.len.toNat := by
  have h_pe_le_adv : (bp.segAt i j).pageEndAddr.toNat ≤
      (bp.elfAt i).advance.toNat :=
    (bp.elfAt i).pageEndAddr_le_advance j.val j.isLt
  have h_base_advance := bp.base_plus_advance_le_rsv_end i
  have h_pageEnd := (bp.segAt i j).pageEndAddr_toNat
  omega

/-- No-wrap of `base + pageVaddr + pageLength` — falls out of
    `segment_pageRange_in_rsv` plus `rsv.noWrap`. -/
theorem segment_pageRange_no_wrap (bp : BasedPlan) (i : Fin bp.n)
    (j : Fin (bp.elfAt i).segments.size) :
    (bp.baseAt i).toNat + (bp.segAt i j).pageVaddr.toNat +
      (bp.segAt i j).pageLength.toNat < 2 ^ 64 := by
  have h_in_rsv := bp.segment_pageRange_in_rsv i j
  have h_rsv := bp.rsv.noWrap
  omega

/-- Helper: `(base + sp.pageVaddr).toNat = base.toNat + sp.pageVaddr.toNat`. -/
theorem segment_base_add_pageVaddr_toNat (bp : BasedPlan) (i : Fin bp.n)
    (j : Fin (bp.elfAt i).segments.size) :
    ((bp.baseAt i) + (bp.segAt i j).pageVaddr).toNat =
    (bp.baseAt i).toNat + (bp.segAt i j).pageVaddr.toNat := by
  have h_no_wrap := bp.segment_pageRange_no_wrap i j
  rw [UInt64.toNat_add]
  exact Nat.mod_eq_of_lt (by omega)

/-- Lower bound: `rsv.addr ≤ baseAt i`. Falls out of `baseAt_toNat`. -/
theorem rsv_addr_le_baseAt (bp : BasedPlan) (i : Fin bp.n) :
    bp.rsv.addr.toNat ≤ (bp.baseAt i).toNat := by
  rw [bp.baseAt_toNat i]
  have h_cum_nonneg : 0 ≤ Plan.cumOffset bp.plan.layout.elfs i.val := Nat.zero_le _
  omega

/-- The mmap range fits in the reservation. -/
theorem segment_mmapRange_in_rsv (bp : BasedPlan) (i : Fin bp.n)
    (j : Fin (bp.elfAt i).segments.size) :
    Runtime.InRange (bp.baseAt i + (bp.segAt i j).pageVaddr)
      (bp.segAt i j).fileOverlayLen bp.rsv.addr bp.rsv.len := by
  have h_pageEnd := bp.segment_pageRange_in_rsv i j
  have h_base_pv := bp.segment_base_add_pageVaddr_toNat i j
  have h_fo_le_pl := (bp.segAt i j).fileOverlay_le_pageLength
  have h_lower := bp.rsv_addr_le_baseAt i
  exact ⟨by rw [h_base_pv]; omega, by rw [h_base_pv]; omega⟩

/-- The mprotect range fits in the reservation. -/
theorem segment_mprotectRange_in_rsv (bp : BasedPlan) (i : Fin bp.n)
    (j : Fin (bp.elfAt i).segments.size) :
    Runtime.InRange (bp.baseAt i + (bp.segAt i j).pageVaddr)
      (bp.segAt i j).pageLength bp.rsv.addr bp.rsv.len := by
  have h_pageEnd := bp.segment_pageRange_in_rsv i j
  have h_base_pv := bp.segment_base_add_pageVaddr_toNat i j
  have h_lower := bp.rsv_addr_le_baseAt i
  exact ⟨by rw [h_base_pv]; omega, by rw [h_base_pv]; omega⟩

/-- The zero range fits in the reservation. -/
theorem segment_zeroRange_in_rsv (bp : BasedPlan) (i : Fin bp.n)
    (j : Fin (bp.elfAt i).segments.size) :
    Runtime.InRange
      (bp.baseAt i + (bp.segAt i j).pageVaddr + (bp.segAt i j).pageInset +
        (bp.segAt i j).segment.filesz)
      (bp.segAt i j).partialBssLen bp.rsv.addr bp.rsv.len := by
  have h_pageEnd := bp.segment_pageRange_in_rsv i j
  have h_no_wrap := bp.segment_pageRange_no_wrap i j
  have h_base_pv := bp.segment_base_add_pageVaddr_toNat i j
  have h_lower := bp.rsv_addr_le_baseAt i
  have h_zero_end := (bp.segAt i j).zero_end_le_pageLength
  have h_vm_le := (bp.segAt i j).vaddr_memsz_le_pageEnd
  have h_filesz_le_memsz :=
    UInt64.le_iff_toNat_le.mp (bp.segAt i j).segment.fileszLeMemsz
  -- Step the address out: (base + pageVaddr + pageInset).toNat.
  have h_a1 : (bp.baseAt i + (bp.segAt i j).pageVaddr).toNat +
              (bp.segAt i j).pageInset.toNat < 2 ^ 64 := by
    rw [h_base_pv]; omega
  have h_a1_eq : (bp.baseAt i + (bp.segAt i j).pageVaddr +
                  (bp.segAt i j).pageInset).toNat =
                 (bp.baseAt i + (bp.segAt i j).pageVaddr).toNat +
                 (bp.segAt i j).pageInset.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_a1
  have h_a2 : (bp.baseAt i + (bp.segAt i j).pageVaddr +
               (bp.segAt i j).pageInset).toNat +
              (bp.segAt i j).segment.filesz.toNat < 2 ^ 64 := by
    rw [h_a1_eq, h_base_pv]; omega
  have h_a2_eq : (bp.baseAt i + (bp.segAt i j).pageVaddr +
                  (bp.segAt i j).pageInset +
                  (bp.segAt i j).segment.filesz).toNat =
                 (bp.baseAt i + (bp.segAt i j).pageVaddr +
                  (bp.segAt i j).pageInset).toNat +
                 (bp.segAt i j).segment.filesz.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_a2
  refine ⟨?_, ?_⟩
  · rw [h_a2_eq, h_a1_eq, h_base_pv]; omega
  · rw [h_a2_eq, h_a1_eq, h_base_pv]; omega

-- ============================================================================
-- Disjointness lemmas. Two flavours:
--   • within-elf — same `i`, distinct segments `j₁ < j₂`. Pulls
--     `Plan.Sorted` (page-aligned non-overlap from ElfLayout) into a
--     `Runtime.Disjoint` claim about the mmap'd ranges.
--   • cross-elf  — distinct elves `i₁ < i₂`. Uses the existing
--     `base_plus_advance_le_base` for the dominant inequality.
--
-- Both end at the same shape: `Disjoint (base + sp.pageVaddr)
-- (fileOverlayLen or pageLength) (base' + sp'.pageVaddr) (...)`.
-- ============================================================================

/-- Within an elf: page-aligned segment ranges don't overlap. Lifts
    `Plan.Sorted` (the existing ElfLayout invariant) from `pageEndAddr ≤
    pageVaddr` to `base + pageEnd ≤ base + pageVaddr'`. -/
theorem within_elf_pageRange_disjoint (bp : BasedPlan) (i : Fin bp.n)
    (j₁ j₂ : Fin (bp.elfAt i).segments.size) (h_lt : j₁ < j₂) :
    Runtime.Disjoint
      (bp.baseAt i + (bp.segAt i j₁).pageVaddr) (bp.segAt i j₁).pageLength
      (bp.baseAt i + (bp.segAt i j₂).pageVaddr) (bp.segAt i j₂).pageLength := by
  have h_pe_le_pv : (bp.segAt i j₁).pageEndAddr ≤ (bp.segAt i j₂).pageVaddr :=
    (bp.elfAt i).segmentsSorted j₁.val j₁.isLt j₂.val j₂.isLt h_lt
  have h_pe_le_pv_nat : (bp.segAt i j₁).pageEndAddr.toNat ≤
      (bp.segAt i j₂).pageVaddr.toNat :=
    UInt64.le_iff_toNat_le.mp h_pe_le_pv
  have h_pe_eq := (bp.segAt i j₁).pageEndAddr_toNat
  have h_base_pv₁ := bp.segment_base_add_pageVaddr_toNat i j₁
  have h_base_pv₂ := bp.segment_base_add_pageVaddr_toNat i j₂
  -- Take left disjunct: end of segment j₁ ≤ start of segment j₂.
  left
  show (bp.baseAt i + (bp.segAt i j₁).pageVaddr).toNat +
       (bp.segAt i j₁).pageLength.toNat ≤
       (bp.baseAt i + (bp.segAt i j₂).pageVaddr).toNat
  rw [h_base_pv₁, h_base_pv₂]
  omega

/-- Within an elf: mmap ranges don't overlap. Shrinks
    `within_elf_pageRange_disjoint` via `fileOverlay_le_pageLength`. -/
theorem within_elf_mmapRange_disjoint (bp : BasedPlan) (i : Fin bp.n)
    (j₁ j₂ : Fin (bp.elfAt i).segments.size) (h_lt : j₁ < j₂) :
    Runtime.Disjoint
      (bp.baseAt i + (bp.segAt i j₁).pageVaddr) (bp.segAt i j₁).fileOverlayLen
      (bp.baseAt i + (bp.segAt i j₂).pageVaddr) (bp.segAt i j₂).fileOverlayLen := by
  have h_page := bp.within_elf_pageRange_disjoint i j₁ j₂ h_lt
  have h_fo₁ := (bp.segAt i j₁).fileOverlay_le_pageLength
  have h_fo₂ := (bp.segAt i j₂).fileOverlay_le_pageLength
  rcases h_page with h_left | h_right
  · left; omega
  · right; omega

/-- Cross-elf: page ranges of any two distinct elves don't overlap.
    Uses `base_plus_advance_le_base` plus `pageEndAddr_le_advance` to
    place the entire page range inside the per-elf slice. -/
theorem cross_elf_pageRange_disjoint (bp : BasedPlan)
    (i₁ i₂ : Fin bp.n) (j₁ : Fin (bp.elfAt i₁).segments.size)
    (j₂ : Fin (bp.elfAt i₂).segments.size) (h_lt : i₁ < i₂) :
    Runtime.Disjoint
      (bp.baseAt i₁ + (bp.segAt i₁ j₁).pageVaddr) (bp.segAt i₁ j₁).pageLength
      (bp.baseAt i₂ + (bp.segAt i₂ j₂).pageVaddr) (bp.segAt i₂ j₂).pageLength := by
  have h_base_pv₁ := bp.segment_base_add_pageVaddr_toNat i₁ j₁
  have h_base_pv₂ := bp.segment_base_add_pageVaddr_toNat i₂ j₂
  have h_pageEnd₁ := bp.segment_pageRange_in_rsv i₁ j₁
  have h_pageEnd₂ := bp.segment_pageRange_in_rsv i₂ j₂
  have h_b_le_b := bp.base_plus_advance_le_base i₁ i₂ h_lt
  -- segment j₁'s page range fits in elf i₁'s [0, advance).
  have h_pe₁ : (bp.segAt i₁ j₁).pageVaddr.toNat +
               (bp.segAt i₁ j₁).pageLength.toNat ≤
               (bp.elfAt i₁).advance.toNat := by
    rw [← (bp.segAt i₁ j₁).pageEndAddr_toNat]
    exact (bp.elfAt i₁).pageEndAddr_le_advance j₁.val j₁.isLt
  left
  show (bp.baseAt i₁ + (bp.segAt i₁ j₁).pageVaddr).toNat +
       (bp.segAt i₁ j₁).pageLength.toNat ≤
       (bp.baseAt i₂ + (bp.segAt i₂ j₂).pageVaddr).toNat
  rw [h_base_pv₁, h_base_pv₂]
  omega

/-- Cross-elf mmap-range disjointness — shrink page-range disjointness
    using `fileOverlay_le_pageLength`. -/
theorem cross_elf_mmapRange_disjoint (bp : BasedPlan)
    (i₁ i₂ : Fin bp.n) (j₁ : Fin (bp.elfAt i₁).segments.size)
    (j₂ : Fin (bp.elfAt i₂).segments.size) (h_lt : i₁ < i₂) :
    Runtime.Disjoint
      (bp.baseAt i₁ + (bp.segAt i₁ j₁).pageVaddr) (bp.segAt i₁ j₁).fileOverlayLen
      (bp.baseAt i₂ + (bp.segAt i₂ j₂).pageVaddr) (bp.segAt i₂ j₂).fileOverlayLen := by
  have h_page := bp.cross_elf_pageRange_disjoint i₁ i₂ j₁ j₂ h_lt
  have h_fo₁ := (bp.segAt i₁ j₁).fileOverlay_le_pageLength
  have h_fo₂ := (bp.segAt i₂ j₂).fileOverlay_le_pageLength
  rcases h_page with h_left | h_right
  · left; omega
  · right; omega

/-- The store range `[base + r_offset, base + r_offset + size)` fits
    in the reservation for any `Entry` with the `coversRela`
    witness on its parent segment. The 4-or-8-byte width is bounded
    by `coversRela`'s conservative 8-byte window. -/
theorem segment_storeRange_in_rsv (bp : BasedPlan) (i : Fin bp.n)
    (j : Fin (bp.elfAt i).segments.size) (r_offset : UInt64)
    (h_cov : Elaborate.coversRela
      (bp.segAt i j).segment.vaddr (bp.segAt i j).segment.memsz r_offset)
    (size : UInt64) (h_size : size.toNat ≤ 8) :
    Runtime.InRange (bp.baseAt i + r_offset) size bp.rsv.addr bp.rsv.len := by
  have h_pageEnd := bp.segment_pageRange_in_rsv i j
  have h_no_wrap := bp.segment_pageRange_no_wrap i j
  have h_vm_le := (bp.segAt i j).vaddr_memsz_le_pageEnd
  obtain ⟨h_vaddr_le, h_ro8_le_vm⟩ := h_cov
  have h_ro_no_wrap : (bp.baseAt i).toNat + r_offset.toNat < 2 ^ 64 := by omega
  have h_base_ro_eq : (bp.baseAt i + r_offset).toNat =
      (bp.baseAt i).toNat + r_offset.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_ro_no_wrap
  have h_lower := bp.rsv_addr_le_baseAt i
  exact ⟨by rw [h_base_ro_eq]; omega, by rw [h_base_ro_eq]; omega⟩

end BasedPlan

end LeanLoad.Materialize

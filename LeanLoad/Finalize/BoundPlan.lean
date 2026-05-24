/-
Base-aware plan: extends `Reloc.Result` with the layout-stage output and the
IO-supplied `Reserve` plus coherence proof. Reads as the pure relocation and
layout facts bound to a concrete reservation — hence "BoundPlan".

`BoundPlan` is the canonical input to `Finalize.build` and
`Finalize.ctorAddrs`. The finalize-stage safety fields on `LoadOps`
are provable structurally from plan invariants. The bounds chain —
`pageEaddr + fileOverlayLen ≤ pageEndAddr ≤ advance` (existing
lemmas in `Layout/Basic.lean`) plus `base + advance ≤ rsv.addr +
rsv.len` (the workhorse `base_plus_advance_le_rsv_end` below) —
has every link as a named lemma.
-/

import LeanLoad.Finalize
import LeanLoad.Layout
import LeanLoad.Reloc

namespace LeanLoad.Finalize

open LeanLoad
open LeanLoad.Parse (Eaddr)
open LeanLoad.Layout (cumOffset cumOffset_succ_of_lt cumOffset_mono
                     assignBases assignBases_at_toNat)

namespace BoundPlan

/-- The number of loaded elves. Used as the `objCount` parameter on downstream
    types (`LoadOps rsvAddr rsvLen objCount`, `SegmentOps rsvAddr rsvLen objCount`, ...). -/
abbrev objCount (bp : BoundPlan) : Nat := bp.graph.objects.size

/-- Per-elf base addresses inside the reservation. `Vector`-typed at
    `bp.objCount`, so `bp.bases[i]` is total for `i : Fin bp.objCount`
    with no size-coherence rewrite. -/
abbrev bases (bp : BoundPlan) : Vector UInt64 bp.objCount :=
  assignBases bp.rsv.addr bp.layout

/-- `0 < bp.objCount` — the main executable is always present. -/
theorem n_pos (bp : BoundPlan) : 0 < bp.objCount :=
  bp.graph.sizePos

/-- Global no-wrap: `rsv.addr + totalSpan` fits in UInt64. Falls out
    of `Reserve.noWrap` plus `h_total`. -/
theorem rsv_noWrap (bp : BoundPlan) :
    bp.rsv.addr.toNat + bp.layout.totalSpan.toNat < 2 ^ 64 := by
  rw [← bp.h_total]; exact bp.rsv.noWrap

-- ============================================================================
-- Fin-indexed accessors. `bp.layout.elfs` and `bp.bases` are both
-- `Vector _ bp.objCount`, so `[i]` is total for `i : Fin bp.objCount`
-- with no proof obligation. All `abbrev` so the underlying form is
-- recovered for unification when needed.
-- ============================================================================

/-- `i`-th elf plan, indexed totally by `Fin bp.objCount`. -/
abbrev elfAt (bp : BoundPlan) (i : Fin bp.objCount) : Layout.ElfLayout bp.objCount :=
  bp.layout.elfs[i]

/-- `i`-th elf's base address. -/
abbrev baseAt (bp : BoundPlan) (i : Fin bp.objCount) : UInt64 :=
  bp.bases[i]

/-- `i`-th elf's open file (held until process exit). -/
abbrev handleAt (bp : BoundPlan) (i : Fin bp.objCount) : Runtime.File :=
  (bp.graph.objects[i.val]'i.isLt).handle

/-- `(i, j)`-th segment plan. -/
abbrev segAt (bp : BoundPlan) (i : Fin bp.objCount)
    (j : Fin (bp.elfAt i).segments.size) : Layout.SegmentLayout bp.objCount :=
  (bp.elfAt i).segments[j]

-- ============================================================================
-- `cumOffset` bridges. The raw lemmas (`cumOffset_succ_of_lt`,
-- `cumOffset_mono`) live on `Array (ElfLayout n)`. The `Vector`-shaped
-- `bp.layout.elfs` projects to that array via `.toArray`; the size
-- equality `size_toArray` lets us convert `Fin bp.objCount` proofs
-- to `i < lp.elfs.toArray.size`.
-- ============================================================================

/-- The elf array's `Array.size` equals `bp.objCount`. Built into
    `Vector` via `Vector.size_toArray`, surfaced here as an `@[simp]`
    handle for proofs. -/
@[simp] theorem elfsArray_size (bp : BoundPlan) :
    bp.layout.elfs.toArray.size = bp.objCount :=
  bp.layout.elfs.size_toArray

private theorem fin_lt_arr (bp : BoundPlan) (i : Fin bp.objCount) :
    i.val < bp.layout.elfs.toArray.size := by
  rw [bp.elfsArray_size]; exact i.isLt

/-- `bp.elfAt i = lp.elfs.toArray[i.val]` — the bridge between Fin-
    indexed `Vector` access and the raw `Array` lemmas. -/
theorem elfAt_eq_toArray_get (bp : BoundPlan) (i : Fin bp.objCount) :
    bp.elfAt i = bp.layout.elfs.toArray[i.val]'(bp.fin_lt_arr i) :=
  rfl

/-- Closed-form for `bp.baseAt i`. -/
theorem baseAt_toNat (bp : BoundPlan) (i : Fin bp.objCount) :
    (bp.baseAt i).toNat =
    bp.rsv.addr.toNat + cumOffset bp.layout.elfs.toArray i.val :=
  assignBases_at_toNat bp.rsv.addr bp.layout bp.rsv_noWrap i

/-- Workhorse: the i-th elf's `[base, base + advance)` fits inside
    `[rsv.addr, rsv.addr + rsv.len)` in `Nat`. Every per-op
    containment proof in `Finalize.LoadOps` chains through this. -/
theorem base_plus_advance_le_rsv_end (bp : BoundPlan) (i : Fin bp.objCount) :
    (bp.baseAt i).toNat + (bp.elfAt i).advance.toNat ≤
    bp.rsv.addr.toNat + bp.rsv.len.toNat := by
  have h_lp : i.val < bp.layout.elfs.toArray.size := bp.fin_lt_arr i
  rw [bp.baseAt_toNat i, bp.h_total, bp.layout.totalSpan_eq, bp.elfAt_eq_toArray_get i]
  have h_succ : cumOffset bp.layout.elfs.toArray i.val +
                (bp.layout.elfs.toArray[i.val]'h_lp).advance.toNat =
                cumOffset bp.layout.elfs.toArray (i.val + 1) :=
    (cumOffset_succ_of_lt _ h_lp).symm
  have h_mono : cumOffset bp.layout.elfs.toArray (i.val + 1) ≤
                cumOffset bp.layout.elfs.toArray bp.layout.elfs.toArray.size :=
    cumOffset_mono _ h_lp
  omega

/-- Each base sits below `rsv.addr + rsv.len`. Consequence of
    `baseAt_toNat` + `cumOffset_mono` + `totalSpan_eq`. -/
theorem baseAt_le_rsv_end (bp : BoundPlan) (i : Fin bp.objCount) :
    (bp.baseAt i).toNat ≤ bp.rsv.addr.toNat + bp.rsv.len.toNat := by
  have h_lp : i.val < bp.layout.elfs.toArray.size := bp.fin_lt_arr i
  rw [bp.baseAt_toNat i, bp.h_total, bp.layout.totalSpan_eq]
  have h_mono : cumOffset bp.layout.elfs.toArray i.val ≤
                cumOffset bp.layout.elfs.toArray bp.layout.elfs.toArray.size :=
    cumOffset_mono _ (Nat.le_of_lt h_lp)
  omega

/-- No-wrap of `baseAt i + delta` when `delta ≤ advance`. The
    arithmetic precondition every UInt64 `(base + addr).toNat`
    decomposition needs. -/
theorem base_add_no_wrap (bp : BoundPlan) (i : Fin bp.objCount) (delta : UInt64)
    (h_delta : delta.toNat ≤ (bp.elfAt i).advance.toNat) :
    (bp.baseAt i).toNat + delta.toNat < 2 ^ 64 := by
  have h_bound := bp.base_plus_advance_le_rsv_end i
  have h_no_wrap := bp.rsv.noWrap
  omega

/-- Across-elf base ordering: `bases[i₁] + advance[i₁] ≤ bases[i₂]`
    whenever `i₁ < i₂`. The cross-elf half of `MmapsDisjoint`. -/
theorem base_plus_advance_le_base (bp : BoundPlan) (i₁ i₂ : Fin bp.objCount)
    (h_lt : i₁ < i₂) :
    (bp.baseAt i₁).toNat + (bp.elfAt i₁).advance.toNat ≤
    (bp.baseAt i₂).toNat := by
  have h_lp₁ : i₁.val < bp.layout.elfs.toArray.size := bp.fin_lt_arr i₁
  rw [bp.baseAt_toNat i₁, bp.baseAt_toNat i₂, bp.elfAt_eq_toArray_get i₁]
  have h_succ : cumOffset bp.layout.elfs.toArray i₁.val +
                (bp.layout.elfs.toArray[i₁.val]'h_lp₁).advance.toNat =
                cumOffset bp.layout.elfs.toArray (i₁.val + 1) :=
    (cumOffset_succ_of_lt _ h_lp₁).symm
  have h_mono : cumOffset bp.layout.elfs.toArray (i₁.val + 1) ≤
                cumOffset bp.layout.elfs.toArray i₂.val :=
    cumOffset_mono _ h_lt
  omega

/-- The main executable's base — total since `bp.objCount > 0`. -/
def mainBase (bp : BoundPlan) : UInt64 :=
  bp.bases[0]'bp.n_pos

-- ============================================================================
-- Per-segment op bounds. Each of these turns a `(bp, i, j)` index
-- into a `Range.InRange` fact about the op `setupSegment` or `bakeReloc`
-- emits at that position. Consumed by `Finalize.Build` to assemble `SegmentOps`
-- proof fields in lock-step with the emitted operations.
-- ============================================================================

/-- The `[base + sp.pageEaddr, base + sp.pageEndAddr)` page-aligned
    range is fully inside `[rsv.addr, rsv.addr + rsv.len)`. This is
    the parent bound — every per-op bound below reduces to it. -/
theorem segment_pageRange_in_rsv (bp : BoundPlan) (i : Fin bp.objCount)
    (j : Fin (bp.elfAt i).segments.size) :
    (bp.baseAt i).toNat + (bp.segAt i j).pageEaddr.toNat +
      (bp.segAt i j).pageLength.toNat ≤
    bp.rsv.addr.toNat + bp.rsv.len.toNat := by
  have h_pe_le_adv : (bp.segAt i j).pageEndAddr.toNat ≤
      (bp.elfAt i).advance.toNat :=
    (bp.elfAt i).pageEndAddr_le_advance j.val j.isLt
  have h_base_advance := bp.base_plus_advance_le_rsv_end i
  have h_pageEnd := (bp.segAt i j).pageEndAddr_toNat
  omega

/-- No-wrap of `base + pageEaddr + pageLength` — falls out of
    `segment_pageRange_in_rsv` plus `rsv.noWrap`. -/
theorem segment_pageRange_no_wrap (bp : BoundPlan) (i : Fin bp.objCount)
    (j : Fin (bp.elfAt i).segments.size) :
    (bp.baseAt i).toNat + (bp.segAt i j).pageEaddr.toNat +
      (bp.segAt i j).pageLength.toNat < 2 ^ 64 := by
  have h_in_rsv := bp.segment_pageRange_in_rsv i j
  have h_rsv := bp.rsv.noWrap
  omega

/-- Helper: `(base + sp.pageEaddr).toNat = base.toNat + sp.pageEaddr.toNat`. -/
theorem segment_base_add_pageEaddr_toNat (bp : BoundPlan) (i : Fin bp.objCount)
    (j : Fin (bp.elfAt i).segments.size) :
    ((bp.baseAt i) + (bp.segAt i j).pageEaddr).toNat =
    (bp.baseAt i).toNat + (bp.segAt i j).pageEaddr.toNat := by
  have h_no_wrap := bp.segment_pageRange_no_wrap i j
  rw [UInt64.toNat_add]
  exact Nat.mod_eq_of_lt (by omega)

/-- Lower bound: `rsv.addr ≤ baseAt i`. Falls out of `baseAt_toNat`. -/
theorem rsv_addr_le_baseAt (bp : BoundPlan) (i : Fin bp.objCount) :
    bp.rsv.addr.toNat ≤ (bp.baseAt i).toNat := by
  rw [bp.baseAt_toNat i]
  have h_cum_nonneg : 0 ≤ Layout.cumOffset bp.layout.elfs.toArray i.val := Nat.zero_le _
  omega

/-- The mmap range fits in the reservation. -/
theorem segment_mmapRange_in_rsv (bp : BoundPlan) (i : Fin bp.objCount)
    (j : Fin (bp.elfAt i).segments.size) :
    Range.InRange (bp.baseAt i + (bp.segAt i j).pageEaddr)
      (bp.segAt i j).fileOverlayLen bp.rsv.addr bp.rsv.len := by
  have h_pageEnd := bp.segment_pageRange_in_rsv i j
  have h_base_pv := bp.segment_base_add_pageEaddr_toNat i j
  have h_fo_le_pl := (bp.segAt i j).fileOverlay_le_pageLength
  have h_lower := bp.rsv_addr_le_baseAt i
  exact ⟨by rw [h_base_pv]; omega, by rw [h_base_pv]; omega⟩

/-- The mprotect range fits in the reservation. -/
theorem segment_mprotectRange_in_rsv (bp : BoundPlan) (i : Fin bp.objCount)
    (j : Fin (bp.elfAt i).segments.size) :
    Range.InRange (bp.baseAt i + (bp.segAt i j).pageEaddr)
      (bp.segAt i j).pageLength bp.rsv.addr bp.rsv.len := by
  have h_pageEnd := bp.segment_pageRange_in_rsv i j
  have h_base_pv := bp.segment_base_add_pageEaddr_toNat i j
  have h_lower := bp.rsv_addr_le_baseAt i
  exact ⟨by rw [h_base_pv]; omega, by rw [h_base_pv]; omega⟩

/-- The zero range fits in the reservation. -/
theorem segment_zeroRange_in_rsv (bp : BoundPlan) (i : Fin bp.objCount)
    (j : Fin (bp.elfAt i).segments.size) :
    Range.InRange
      (bp.baseAt i + (bp.segAt i j).pageEaddr + (bp.segAt i j).pageInset +
        (bp.segAt i j).segment.filesz.val)
      (bp.segAt i j).partialBssLen bp.rsv.addr bp.rsv.len := by
  have h_pageEnd := bp.segment_pageRange_in_rsv i j
  have h_no_wrap := bp.segment_pageRange_no_wrap i j
  have h_base_pv := bp.segment_base_add_pageEaddr_toNat i j
  have h_lower := bp.rsv_addr_le_baseAt i
  have h_zero_end := (bp.segAt i j).zero_end_le_pageLength
  have h_vm_le := (bp.segAt i j).vaddr_memsz_le_pageEnd
  have h_filesz_le_memsz := (bp.segAt i j).segment.fileszLeMemsz
  -- Step the address out: (base + pageEaddr + pageInset).toNat.
  have h_a1 : (bp.baseAt i + (bp.segAt i j).pageEaddr).toNat +
              (bp.segAt i j).pageInset.toNat < 2 ^ 64 := by
    rw [h_base_pv]; omega
  have h_a1_eq : (bp.baseAt i + (bp.segAt i j).pageEaddr +
                  (bp.segAt i j).pageInset).toNat =
                 (bp.baseAt i + (bp.segAt i j).pageEaddr).toNat +
                 (bp.segAt i j).pageInset.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_a1
  have h_a2 : (bp.baseAt i + (bp.segAt i j).pageEaddr +
               (bp.segAt i j).pageInset).toNat +
              (bp.segAt i j).segment.filesz.toNat < 2 ^ 64 := by
    rw [h_a1_eq, h_base_pv]; omega
  have h_a2_eq : (bp.baseAt i + (bp.segAt i j).pageEaddr +
                  (bp.segAt i j).pageInset +
                  (bp.segAt i j).segment.filesz.val).toNat =
                 (bp.baseAt i + (bp.segAt i j).pageEaddr +
                  (bp.segAt i j).pageInset).toNat +
                 (bp.segAt i j).segment.filesz.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_a2
  refine ⟨?_, ?_⟩
  · rw [h_a2_eq, h_a1_eq, h_base_pv]; omega
  · rw [h_a2_eq, h_a1_eq, h_base_pv]; omega

-- ============================================================================
-- Disjointness lemmas. Two flavours:
--   • within-elf — same `i`, distinct segments `j₁ < j₂`. Pulls
--     `Layout.Sorted` (page-aligned non-overlap from ElfLayout) into a
--     `Range.Disjoint` claim about the mmap'd ranges.
--   • cross-elf  — distinct elves `i₁ < i₂`. Uses the existing
--     `base_plus_advance_le_base` for the dominant inequality.
--
-- Both end at the same shape: `Range.Disjoint (base + sp.pageEaddr)
-- (fileOverlayLen or pageLength) (base' + sp'.pageEaddr) (...)`.
-- ============================================================================

/-- Within an elf: page-aligned segment ranges don't overlap. Lifts
    `Layout.Sorted` (the existing ElfLayout invariant) from `pageEndAddr ≤
    pageEaddr` to `base + pageEnd ≤ base + pageEaddr'`. -/
theorem within_elf_pageRange_disjoint (bp : BoundPlan) (i : Fin bp.objCount)
    (j₁ j₂ : Fin (bp.elfAt i).segments.size) (h_lt : j₁ < j₂) :
    Range.Disjoint
      (bp.baseAt i + (bp.segAt i j₁).pageEaddr) (bp.segAt i j₁).pageLength
      (bp.baseAt i + (bp.segAt i j₂).pageEaddr) (bp.segAt i j₂).pageLength := by
  have h_pe_le_pv : (bp.segAt i j₁).pageEndAddr ≤ (bp.segAt i j₂).pageEaddr :=
    (bp.elfAt i).segmentsSorted j₁.val j₁.isLt j₂.val j₂.isLt h_lt
  have h_pe_le_pv_nat : (bp.segAt i j₁).pageEndAddr.toNat ≤
      (bp.segAt i j₂).pageEaddr.toNat :=
    UInt64.le_iff_toNat_le.mp h_pe_le_pv
  have h_pe_eq := (bp.segAt i j₁).pageEndAddr_toNat
  have h_base_pv₁ := bp.segment_base_add_pageEaddr_toNat i j₁
  have h_base_pv₂ := bp.segment_base_add_pageEaddr_toNat i j₂
  -- Take left disjunct: end of segment j₁ ≤ start of segment j₂.
  left
  show (bp.baseAt i + (bp.segAt i j₁).pageEaddr).toNat +
       (bp.segAt i j₁).pageLength.toNat ≤
       (bp.baseAt i + (bp.segAt i j₂).pageEaddr).toNat
  rw [h_base_pv₁, h_base_pv₂]
  omega

/-- Within an elf: mmap ranges don't overlap. Shrinks
    `within_elf_pageRange_disjoint` via `fileOverlay_le_pageLength`. -/
theorem within_elf_mmapRange_disjoint (bp : BoundPlan) (i : Fin bp.objCount)
    (j₁ j₂ : Fin (bp.elfAt i).segments.size) (h_lt : j₁ < j₂) :
    Range.Disjoint
      (bp.baseAt i + (bp.segAt i j₁).pageEaddr) (bp.segAt i j₁).fileOverlayLen
      (bp.baseAt i + (bp.segAt i j₂).pageEaddr) (bp.segAt i j₂).fileOverlayLen := by
  have h_page := bp.within_elf_pageRange_disjoint i j₁ j₂ h_lt
  have h_fo₁ := (bp.segAt i j₁).fileOverlay_le_pageLength
  have h_fo₂ := (bp.segAt i j₂).fileOverlay_le_pageLength
  rcases h_page with h_left | h_right
  · left; omega
  · right; omega

/-- Cross-elf: page ranges of any two distinct elves don't overlap.
    Uses `base_plus_advance_le_base` plus `pageEndAddr_le_advance` to
    place the entire page range inside the per-elf slice. -/
theorem cross_elf_pageRange_disjoint (bp : BoundPlan)
    (i₁ i₂ : Fin bp.objCount) (j₁ : Fin (bp.elfAt i₁).segments.size)
    (j₂ : Fin (bp.elfAt i₂).segments.size) (h_lt : i₁ < i₂) :
    Range.Disjoint
      (bp.baseAt i₁ + (bp.segAt i₁ j₁).pageEaddr) (bp.segAt i₁ j₁).pageLength
      (bp.baseAt i₂ + (bp.segAt i₂ j₂).pageEaddr) (bp.segAt i₂ j₂).pageLength := by
  have h_base_pv₁ := bp.segment_base_add_pageEaddr_toNat i₁ j₁
  have h_base_pv₂ := bp.segment_base_add_pageEaddr_toNat i₂ j₂
  have h_pageEnd₁ := bp.segment_pageRange_in_rsv i₁ j₁
  have h_pageEnd₂ := bp.segment_pageRange_in_rsv i₂ j₂
  have h_b_le_b := bp.base_plus_advance_le_base i₁ i₂ h_lt
  -- segment j₁'s page range fits in elf i₁'s [0, advance).
  have h_pe₁ : (bp.segAt i₁ j₁).pageEaddr.toNat +
               (bp.segAt i₁ j₁).pageLength.toNat ≤
               (bp.elfAt i₁).advance.toNat := by
    rw [← (bp.segAt i₁ j₁).pageEndAddr_toNat]
    exact (bp.elfAt i₁).pageEndAddr_le_advance j₁.val j₁.isLt
  left
  show (bp.baseAt i₁ + (bp.segAt i₁ j₁).pageEaddr).toNat +
       (bp.segAt i₁ j₁).pageLength.toNat ≤
       (bp.baseAt i₂ + (bp.segAt i₂ j₂).pageEaddr).toNat
  rw [h_base_pv₁, h_base_pv₂]
  omega

/-- Cross-elf mmap-range disjointness — shrink page-range disjointness
    using `fileOverlay_le_pageLength`. -/
theorem cross_elf_mmapRange_disjoint (bp : BoundPlan)
    (i₁ i₂ : Fin bp.objCount) (j₁ : Fin (bp.elfAt i₁).segments.size)
    (j₂ : Fin (bp.elfAt i₂).segments.size) (h_lt : i₁ < i₂) :
    Range.Disjoint
      (bp.baseAt i₁ + (bp.segAt i₁ j₁).pageEaddr) (bp.segAt i₁ j₁).fileOverlayLen
      (bp.baseAt i₂ + (bp.segAt i₂ j₂).pageEaddr) (bp.segAt i₂ j₂).fileOverlayLen := by
  have h_page := bp.cross_elf_pageRange_disjoint i₁ i₂ j₁ j₂ h_lt
  have h_fo₁ := (bp.segAt i₁ j₁).fileOverlay_le_pageLength
  have h_fo₂ := (bp.segAt i₂ j₂).fileOverlay_le_pageLength
  rcases h_page with h_left | h_right
  · left; omega
  · right; omega

/-- The store range `[base + r_offset, base + r_offset + size)` fits
    in the reservation for any `Entry` with the `Reloc.covered`
    witness on its parent segment. The 4-or-8-byte width is bounded
    by `Reloc.covered`'s conservative 8-byte window. -/
theorem segment_storeRange_in_rsv (bp : BoundPlan) (i : Fin bp.objCount)
    (j : Fin (bp.elfAt i).segments.size) (r_offset : Eaddr)
    (h_cov : (bp.segAt i j).segment.eaddr.toNat ≤ r_offset.toNat ∧
      r_offset.toNat + 8 ≤
        (bp.segAt i j).segment.eaddr.toNat + (bp.segAt i j).segment.memsz.toNat)
    (size : UInt64) (h_size : size.toNat ≤ 8) :
    Range.InRange (bp.baseAt i + r_offset.val) size bp.rsv.addr bp.rsv.len := by
  have h_pageEnd := bp.segment_pageRange_in_rsv i j
  have h_no_wrap := bp.segment_pageRange_no_wrap i j
  have h_vm_le := (bp.segAt i j).vaddr_memsz_le_pageEnd
  obtain ⟨h_vaddr_le, h_ro8_le_vm⟩ := h_cov
  have h_ro_no_wrap : (bp.baseAt i).toNat + r_offset.toNat < 2 ^ 64 := by omega
  have h_base_ro_eq : (bp.baseAt i + r_offset.val).toNat =
      (bp.baseAt i).toNat + r_offset.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_ro_no_wrap
  have h_lower := bp.rsv_addr_le_baseAt i
  exact ⟨by rw [h_base_ro_eq]; omega, by rw [h_base_ro_eq]; omega⟩

end BoundPlan

end LeanLoad.Finalize

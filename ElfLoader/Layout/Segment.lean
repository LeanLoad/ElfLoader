/-
Per-segment plan — base-free.

A `SegmentLayout objCount` lifts one PT_LOAD `Segment` into the loader's view:
page math precomputed once, stored as fields, plus the five
per-segment invariants the finalize-stage safety proofs read by
direct projection (`sp.pageEnd_lt`, `sp.fileOverlay_le_pageLength`, …):

  • `pageEnd_lt`         — `pageEaddr + pageLength < 2^64` (no wrap).
  • `fileOverlay_le_pageLength` — `fileOverlayLen ≤ pageLength`.
  • `vaddr_memsz_le_pageEnd`    — `eaddr + memsz ≤ pageEaddr + pageLength`
                                  (store-window upper bound for relocs).
  • `zero_end_le_pageLength`    — `pageInset + filesz + partialBssLen ≤
                                   pageLength` (BSS-zero op upper bound).
  • `pageInset_eq_vaddr` — `pageEaddr + pageInset = eaddr` (lets
                           per-op proofs rewrite to canonical form).

Also carries `relocs : Array (Entry objCount segment)` — the per-segment
planned relocations; every offset is base-free (relative to base = 0)
and the exec builder adds the chosen base when emitting structured ops.

`ofSegmentCore` is the only constructor; it discharges all five
invariant fields at construction via the raw helper lemmas in this
file (`raw_pageEnd_lt`, `raw_fileOverlay_le_pageLength`, …).

Spec: gabi 07 § Program Header (page-aligned mmap views).
-/

import ElfLoader.Layout.Align
import ElfLoader.Reloc
import ElfLoader.Parse
import ElfLoader.Parse.LoadMap.Segment.Basic
import ElfLoader.Parse.LoadMap.ProgramHeader.Basic

namespace ElfLoader.Layout

open ElfLoader
open ElfLoader.Parse
open ElfLoader.Reloc (Entry)

-- ============================================================================
-- Raw page-arithmetic helpers — about `Segment` + alignDown/alignUp
-- expressions, no `SegmentLayout` reference. Used by `SegmentLayout.ofSegmentCore`
-- to discharge each per-segment invariant field.
-- ============================================================================

namespace SegmentLayout

/-- `effectiveAlign` is the same alignment expression checked by
    `Segment.pageLayoutNoWrap`. -/
private theorem pageLayoutNoWrap {fileSize : ByteSize} (s : Segment fileSize) :
    s.eaddr.toNat + s.memsz.toNat + (effectiveAlign s.align).toNat < 2 ^ 64 := by
  simpa [Segment.eaddr, Segment.memsz, Segment.align, effectiveAlign, segmentLayoutAlign]
    using s.pageLayoutNoWrap

/-- `eaddr + memsz` doesn't wrap, given `Segment.eaddrNoWrap`. -/
private theorem vaddr_add_memsz_toNat {fileSize : ByteSize} (s : Segment fileSize) :
    (s.eaddr.val + s.memsz.val).toNat = s.eaddr.toNat + s.memsz.toNat := by
  have h_no_wrap : s.eaddr.toNat + s.memsz.toNat < 2 ^ 64 := by
    simpa [Segment.eaddr, Segment.memsz] using s.eaddrNoWrap
  rw [UInt64.toNat_add]
  exact Nat.mod_eq_of_lt h_no_wrap

/-- `effectiveAlign align ≤ align + 1` (toNat). -/
theorem effectiveAlign_le_succ (align : UInt64) :
    (effectiveAlign align).toNat ≤ align.toNat + 1 := by
  change (if align == 0 then (1 : UInt64) else align).toNat ≤ align.toNat + 1
  split <;> rename_i h
  · have h_eq : align = 0 := by simpa using h
    rw [h_eq]; decide
  · omega

/-- `alignDown s.eaddr ea ≤ alignUp (s.eaddr + s.memsz) ea` —
    page-aligned start ≤ page-aligned end. Prerequisite for
    `pageLength`'s subtraction to be well-defined. -/
private theorem pageEaddr_le_pageEnd_raw {fileSize : ByteSize} (s : Segment fileSize) :
    alignDown s.eaddr.val (effectiveAlign s.align) ≤
    alignUp (s.eaddr.val + s.memsz.val) (effectiveAlign s.align) := by
  have h_ea_ne : effectiveAlign s.align ≠ 0 :=
    effectiveAlign_ne_zero s.align
  have h1 := alignDown_le s.eaddr.val (effectiveAlign s.align)
  have h2 : s.eaddr.val ≤ s.eaddr.val + s.memsz.val := by
    rw [UInt64.le_iff_toNat_le, vaddr_add_memsz_toNat]
    simp [Eaddr.toNat, ByteSize.toNat]
  have h_au_no_wrap : (s.eaddr.val + s.memsz.val).toNat +
      (effectiveAlign s.align).toNat < 2 ^ 64 := by
    rw [vaddr_add_memsz_toNat]
    exact pageLayoutNoWrap s
  have h3 : s.eaddr.val + s.memsz.val ≤
      alignUp (s.eaddr.val + s.memsz.val) (effectiveAlign s.align) :=
    alignUp_ge _ _ h_ea_ne h_au_no_wrap
  rw [UInt64.le_iff_toNat_le] at h1 h2 h3 ⊢
  omega

/-- `(alignUp (s.eaddr + s.memsz) ea).toNat ≤ s.eaddr + s.memsz + ea`.
    Exposed for `Layout.Elf`'s `ElfLayout.ofElf` proof. -/
theorem alignUp_vm_le {fileSize : ByteSize} (s : Segment fileSize) :
    (alignUp (s.eaddr.val + s.memsz.val) (effectiveAlign s.align)).toNat ≤
    s.eaddr.toNat + s.memsz.toNat + (effectiveAlign s.align).toNat := by
  have h_ea_ne : effectiveAlign s.align ≠ 0 := effectiveAlign_ne_zero s.align
  have h_au_no_wrap : (s.eaddr.val + s.memsz.val).toNat +
      (effectiveAlign s.align).toNat < 2 ^ 64 := by
    rw [vaddr_add_memsz_toNat]
    exact pageLayoutNoWrap s
  have h_au_le := alignUp_le_add_align _ _ h_ea_ne h_au_no_wrap
  rw [vaddr_add_memsz_toNat] at h_au_le
  exact h_au_le

/-- `(alignUp (s.eaddr + s.memsz) ea).toNat < 2^64`. -/
private theorem alignUp_vm_lt {fileSize : ByteSize} (s : Segment fileSize) :
    (alignUp (s.eaddr.val + s.memsz.val) (effectiveAlign s.align)).toNat < 2 ^ 64 := by
  have h := alignUp_vm_le s
  have h_no_wrap : s.eaddr.toNat + s.memsz.toNat +
      (effectiveAlign s.align).toNat < 2 ^ 64 := pageLayoutNoWrap s
  omega

/-- `s.eaddr + s.memsz ≤ alignUp (s.eaddr + s.memsz) ea` (toNat). -/
private theorem vm_le_alignUp_vm {fileSize : ByteSize} (s : Segment fileSize) :
    s.eaddr.toNat + s.memsz.toNat ≤
    (alignUp (s.eaddr.val + s.memsz.val) (effectiveAlign s.align)).toNat := by
  rw [← vaddr_add_memsz_toNat]
  apply UInt64.le_iff_toNat_le.mp
  have h_ea_ne : effectiveAlign s.align ≠ 0 := effectiveAlign_ne_zero s.align
  have h_no_wrap : (s.eaddr.val + s.memsz.val).toNat +
      (effectiveAlign s.align).toNat < 2 ^ 64 := by
    rw [vaddr_add_memsz_toNat]
    exact pageLayoutNoWrap s
  exact alignUp_ge _ _ h_ea_ne h_no_wrap

/-- The `pageEnd - pageEaddr` UInt64 subtraction equals the Nat-level
    difference `pageEnd.toNat - pageEaddr.toNat`.
    Exposed for `Layout.Elf`'s `ElfLayout.ofElf` proof. -/
theorem pageLength_toNat {fileSize : ByteSize} (s : Segment fileSize) :
    (alignUp (s.eaddr.val + s.memsz.val) (effectiveAlign s.align) -
      alignDown s.eaddr.val (effectiveAlign s.align)).toNat =
    (alignUp (s.eaddr.val + s.memsz.val) (effectiveAlign s.align)).toNat -
    (alignDown s.eaddr.val (effectiveAlign s.align)).toNat :=
  UInt64.toNat_sub_of_le _ _ (pageEaddr_le_pageEnd_raw s)

/-- `pageEaddr + pageLength = pageEnd` (in `Nat`). -/
private theorem pageEaddr_add_pageLength_raw {fileSize : ByteSize} (s : Segment fileSize) :
    (alignDown s.eaddr.val (effectiveAlign s.align)).toNat +
    (alignUp (s.eaddr.val + s.memsz.val) (effectiveAlign s.align) -
      alignDown s.eaddr.val (effectiveAlign s.align)).toNat =
    (alignUp (s.eaddr.val + s.memsz.val) (effectiveAlign s.align)).toNat := by
  rw [pageLength_toNat]
  have := UInt64.le_iff_toNat_le.mp (pageEaddr_le_pageEnd_raw s)
  omega

/-- The `pageEaddr + pageLength < 2^64` bound — used as
    `SegmentLayout.pageEnd_lt`. -/
private theorem raw_pageEnd_lt {fileSize : ByteSize} (s : Segment fileSize) :
    (alignDown s.eaddr.val (effectiveAlign s.align)).toNat +
    (alignUp (s.eaddr.val + s.memsz.val) (effectiveAlign s.align) -
      alignDown s.eaddr.val (effectiveAlign s.align)).toNat < 2 ^ 64 := by
  rw [pageEaddr_add_pageLength_raw]; exact alignUp_vm_lt s

/-- The `eaddr + memsz ≤ pageEaddr + pageLength` bound — used as
    `SegmentLayout.vaddr_memsz_le_pageEnd`. -/
private theorem raw_vaddr_memsz_le_pageEnd {fileSize : ByteSize} (s : Segment fileSize) :
    s.eaddr.toNat + s.memsz.toNat ≤
    (alignDown s.eaddr.val (effectiveAlign s.align)).toNat +
    (alignUp (s.eaddr.val + s.memsz.val) (effectiveAlign s.align) -
      alignDown s.eaddr.val (effectiveAlign s.align)).toNat := by
  rw [pageEaddr_add_pageLength_raw]; exact vm_le_alignUp_vm s

/-- The `pageEaddr + pageInset = eaddr` equality — used as
    `SegmentLayout.pageInset_eq_vaddr`. -/
private theorem raw_pageInset_eq_vaddr {fileSize : ByteSize} (s : Segment fileSize) :
    (alignDown s.eaddr.val (effectiveAlign s.align)).toNat +
    (s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)).toNat =
    s.eaddr.toNat := by
  have h_ad_le : alignDown s.eaddr.val (effectiveAlign s.align) ≤ s.eaddr.val :=
    alignDown_le _ _
  have h_pi_eq : (s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)).toNat =
                 s.eaddr.toNat - (alignDown s.eaddr.val (effectiveAlign s.align)).toNat :=
    UInt64.toNat_sub_of_le _ _ h_ad_le
  rw [h_pi_eq]
  have h_ad_nat := UInt64.le_iff_toNat_le.mp h_ad_le
  simp [Eaddr.toNat] at h_ad_nat ⊢
  omega

/-- `pageEaddr + fileOverlayLen ≤ pageEaddr + pageLength` (in `Nat`). -/
private theorem pageEaddr_add_fileOverlayLen_le_pageEnd {fileSize : ByteSize}
    (s : Segment fileSize) :
    (alignDown s.eaddr.val (effectiveAlign s.align)).toNat +
    (alignUp ((s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)) +
              s.filesz.val) (effectiveAlign s.align)).toNat ≤
    (alignDown s.eaddr.val (effectiveAlign s.align)).toNat +
    (alignUp (s.eaddr.val + s.memsz.val) (effectiveAlign s.align) -
      alignDown s.eaddr.val (effectiveAlign s.align)).toNat := by
  rw [pageEaddr_add_pageLength_raw]
  have h_ea_ne : effectiveAlign s.align ≠ 0 := effectiveAlign_ne_zero s.align
  have h_filesz_le_memsz : s.filesz.toNat ≤ s.memsz.toNat :=
    s.fileszLeMemsz
  have h_layout := pageLayoutNoWrap s
  have h_ea_le := effectiveAlign_le_succ s.align
  have h_ad_le_v : (alignDown s.eaddr.val (effectiveAlign s.align)).toNat ≤ s.eaddr.toNat :=
    UInt64.le_iff_toNat_le.mp (alignDown_le _ _)
  have h_pi_eq : (s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)).toNat =
                 s.eaddr.toNat - (alignDown s.eaddr.val (effectiveAlign s.align)).toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (alignDown_le _ _)]
    simp [Eaddr.toNat]
  have h_py_no_wrap : (s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)).toNat +
      s.filesz.toNat < 2 ^ 64 := by rw [h_pi_eq]; omega
  have h_py_eq :
      ((s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)) + s.filesz.val).toNat =
                 (s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)).toNat +
                 s.filesz.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_py_no_wrap
  have h_y_no_wrap :
      ((s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)) + s.filesz.val).toNat +
      (effectiveAlign s.align).toNat < 2 ^ 64 := by
    rw [h_py_eq, h_pi_eq]; omega
  have h_sum_no_wrap : (alignDown s.eaddr.val (effectiveAlign s.align)).toNat +
      ((s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)) + s.filesz.val).toNat +
      (effectiveAlign s.align).toNat < 2 ^ 64 := by
    rw [h_py_eq, h_pi_eq]; omega
  rw [alignDown_add_alignUp_toNat _ _ _ h_ea_ne h_y_no_wrap h_sum_no_wrap]
  have h_vf_no_wrap : s.eaddr.toNat + s.filesz.toNat < 2 ^ 64 := by omega
  have h_combined :
      alignDown s.eaddr.val (effectiveAlign s.align) +
      ((s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)) + s.filesz.val) =
      s.eaddr.val + s.filesz.val := by
    have h_ad_le_raw :
        (alignDown s.eaddr.val (effectiveAlign s.align)).toNat ≤ s.eaddr.val.toNat :=
      UInt64.le_iff_toNat_le.mp (alignDown_le _ _)
    have h_pi_eq_raw :
        (s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)).toNat =
          s.eaddr.val.toNat - (alignDown s.eaddr.val (effectiveAlign s.align)).toNat :=
      UInt64.toNat_sub_of_le _ _ (alignDown_le _ _)
    have h_py_no_wrap_raw :
        (s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)).toNat +
          s.filesz.val.toNat < 2 ^ 64 := by
      simpa [Segment.filesz, ByteSize.toNat] using h_py_no_wrap
    have h_py_eq_raw :
        ((s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)) + s.filesz.val).toNat =
          (s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)).toNat +
            s.filesz.val.toNat := by
      rw [UInt64.toNat_add]
      exact Nat.mod_eq_of_lt h_py_no_wrap_raw
    have h_vf_no_wrap_raw : s.eaddr.val.toNat + s.filesz.val.toNat < 2 ^ 64 := by
      simpa [Segment.eaddr, Segment.filesz, Eaddr.toNat, ByteSize.toNat] using h_vf_no_wrap
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, h_py_eq_raw, h_pi_eq_raw, UInt64.toNat_add]
    have h_inner_no_wrap_raw :
        (alignDown s.eaddr.val (effectiveAlign s.align)).toNat +
          (s.eaddr.val.toNat -
              (alignDown s.eaddr.val (effectiveAlign s.align)).toNat +
            s.filesz.val.toNat) < 2 ^ 64 := by
      omega
    rw [Nat.mod_eq_of_lt h_inner_no_wrap_raw, Nat.mod_eq_of_lt h_vf_no_wrap_raw]
    omega
  rw [h_combined]
  have h_vf_eq : (s.eaddr.val + s.filesz.val).toNat = s.eaddr.toNat + s.filesz.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_vf_no_wrap
  have h_vm_eq : (s.eaddr.val + s.memsz.val).toNat = s.eaddr.toNat + s.memsz.toNat :=
    vaddr_add_memsz_toNat s
  apply alignUp_mono_toNat _ _ _ h_ea_ne
  · rw [h_vf_eq]; omega
  · rw [h_vm_eq]; exact h_layout
  · rw [h_vf_eq, h_vm_eq]; omega

/-- The `fileOverlayLen ≤ pageLength` bound — used as
    `SegmentLayout.fileOverlay_le_pageLength`. -/
private theorem raw_fileOverlay_le_pageLength {fileSize : ByteSize} (s : Segment fileSize) :
    (alignUp ((s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)) +
              s.filesz.val) (effectiveAlign s.align)).toNat ≤
    (alignUp (s.eaddr.val + s.memsz.val) (effectiveAlign s.align) -
      alignDown s.eaddr.val (effectiveAlign s.align)).toNat := by
  have h := pageEaddr_add_fileOverlayLen_le_pageEnd s
  omega

/-- The `pageInset + filesz + partialBssLen ≤ pageLength` bound —
    used as `SegmentLayout.zero_end_le_pageLength`. -/
private theorem raw_zero_end_le_pageLength {fileSize : ByteSize} (s : Segment fileSize) :
    (s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)).toNat +
    s.filesz.toNat +
    (alignUp ((s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)) +
              s.filesz.val) (effectiveAlign s.align) -
      ((s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)) + s.filesz.val)).toNat ≤
    (alignUp (s.eaddr.val + s.memsz.val) (effectiveAlign s.align) -
      alignDown s.eaddr.val (effectiveAlign s.align)).toNat := by
  -- partialBssLen = fileOverlayLen - (pageInset + filesz) in UInt64.
  -- We show pageInset + filesz ≤ fileOverlayLen (from `alignUp_ge`), so
  -- pageInset + filesz + partialBssLen = fileOverlayLen ≤ pageLength.
  have h_ea_ne : effectiveAlign s.align ≠ 0 := effectiveAlign_ne_zero s.align
  have h_pi_eq : (s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)).toNat =
                 s.eaddr.toNat -
                 (alignDown s.eaddr.val (effectiveAlign s.align)).toNat :=
    by
      rw [UInt64.toNat_sub_of_le _ _ (alignDown_le _ _)]
      simp [Eaddr.toNat]
  have h_ad_le : (alignDown s.eaddr.val (effectiveAlign s.align)).toNat ≤
                 s.eaddr.toNat :=
    UInt64.le_iff_toNat_le.mp (alignDown_le _ _)
  have h_fm : s.filesz.toNat ≤ s.memsz.toNat := by
    simpa [Segment.filesz, Segment.memsz] using s.fileszLeMemsz
  have h_layout := pageLayoutNoWrap s
  have h_ea_le_succ := effectiveAlign_le_succ s.align
  have h_pi_filesz_no_wrap :
      (s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)).toNat +
      s.filesz.toNat < 2 ^ 64 := by
    rw [h_pi_eq]
    have h_layout' := h_layout
    have h_fm' := h_fm
    simp [Segment.eaddr, Segment.memsz, Segment.filesz, Eaddr.toNat, ByteSize.toNat]
      at h_layout' h_fm' ⊢
    omega
  have h_pi_filesz_eq :
      ((s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)) + s.filesz.val).toNat =
      (s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)).toNat +
      s.filesz.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_pi_filesz_no_wrap
  have h_y_no_wrap :
      ((s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)) + s.filesz.val).toNat +
      (effectiveAlign s.align).toNat < 2 ^ 64 := by
    rw [h_pi_filesz_eq, h_pi_eq]
    have h_layout' := h_layout
    have h_fm' := h_fm
    simp [Segment.eaddr, Segment.memsz, Segment.filesz, Eaddr.toNat, ByteSize.toNat]
      at h_layout' h_fm' ⊢
    omega
  have h_pi_filesz_le_fol :
      ((s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)) + s.filesz.val).toNat ≤
      (alignUp ((s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)) +
                s.filesz.val) (effectiveAlign s.align)).toNat :=
    UInt64.le_iff_toNat_le.mp (alignUp_ge _ _ h_ea_ne h_y_no_wrap)
  have h_partial_eq :
      (alignUp ((s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)) +
                s.filesz.val) (effectiveAlign s.align) -
        ((s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)) +
          s.filesz.val)).toNat =
      (alignUp ((s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)) +
                s.filesz.val) (effectiveAlign s.align)).toNat -
      ((s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)) + s.filesz.val).toNat :=
    UInt64.toNat_sub_of_le _ _
      (UInt64.le_iff_toNat_le.mpr h_pi_filesz_le_fol)
  have h_fo_le_pl := raw_fileOverlay_le_pageLength s
  rw [h_partial_eq, h_pi_filesz_eq]
  omega

end SegmentLayout

-- ============================================================================
-- SegmentLayout objCount — one PT_LOAD with page math + per-segment invariants
-- + per-segment relocs. Base-free: every offset is relative to base = 0.
-- ============================================================================

/-- A `Segment` lifted to the loader's view. All page math is
    precomputed once via `ofSegmentCore`; addresses are relative to
    `base = 0`. Per-segment invariants live as Prop fields so consumers
    project them directly (`sp.pageEnd_lt`) — there is no
    `∀ j, ∀ h : j < segs.size, …` quantifier on `ElfLayout` to peel.

    `relocs` is the per-segment planned-relocation array (built parallel
    to construction in `ElfLayout.ofElfCore`). -/
structure SegmentLayout (objCount : Nat) where
  /-- Underlying gabi segment. Carries `rela`/`jmprel` for reloc
      planning plus range/page-layout no-wrap witnesses for proofs. -/
  fileSize       : ByteSize
  segment        : Segment fileSize
  /-- `alignDown eaddr ea` — page-aligned start. -/
  pageEaddr      : UInt64
  /-- Total page-aligned mmap length. -/
  pageLength     : UInt64
  /-- `eaddr − pageEaddr`. Distance from page start to first useful byte. -/
  pageInset      : UInt64
  /-- Page-aligned length of the file-backed overlay. Zero when `filesz = 0`. -/
  fileOverlayLen : UInt64
  /-- Page-aligned file offset for the overlay's `mmap(2)`. -/
  fileOffset     : UInt64
  /-- Bytes from `filesz` to the overlay's page-aligned end —
      file-mapped (not zero-guaranteed), explicitly zeroed via the
      per-segment `ZeroOp`. -/
  partialBssLen  : UInt64
  /-- POSIX `PROT_*` bits derived from gabi `PF_*`. -/
  prot           : UInt32
  /-- `pageEaddr + pageLength < 2^64` — the finalize-stage UInt64
      addition lifts to `Nat` without wrap. -/
  pageEnd_lt : pageEaddr.toNat + pageLength.toNat < 2 ^ 64
  /-- The file overlay sits inside the page-aligned segment range —
      the `SegmentOps.mmapInRange` bound. -/
  fileOverlay_le_pageLength : fileOverlayLen.toNat ≤ pageLength.toNat
  /-- The 4/8-byte write window of any rela sits inside the
      page-aligned segment range — combines with `Reloc.covered` to
      discharge `SegmentOps.storesInRange`. -/
  vaddr_memsz_le_pageEnd : segment.eaddr.toNat + segment.memsz.toNat ≤
    pageEaddr.toNat + pageLength.toNat
  /-- The partial-page BSS zero op's end sits inside the
      page-aligned segment range — the `SegmentOps.zeroInRange`
      bound. -/
  zero_end_le_pageLength : pageInset.toNat + segment.filesz.toNat +
    partialBssLen.toNat ≤ pageLength.toNat
  /-- The zero op starts at `pageEaddr + pageInset = eaddr`. Lets
      the zero op's absolute address simplify to `base + eaddr +
      filesz` for proofs. -/
  pageInset_eq_vaddr : pageEaddr.toNat + pageInset.toNat = segment.eaddr.toNat
  /-- Planned relocations targeting this segment, in
      `Parse.Reloc.RelocTable.rela ++ Parse.Reloc.RelocTable.jmprel` order. Each
      entry carries its `Reloc.covered` witness keyed to `segment` so
      `SegmentOps.storesInRange` is structurally provable.
      `Finalize.bakeSegmentRelocs` reads this directly. -/
  relocs         : Array (Entry objCount segment)

namespace SegmentLayout

/-- Compute the page-math view of a `Segment` and discharge each
    per-segment invariant. Callers supply `relocs` separately
    (typically via `Reloc.planSegment`). -/
def ofSegmentCore (objCount : Nat) {fileSize : ByteSize}
    (s : Segment fileSize) (relocs : Array (Entry objCount s)) :
    SegmentLayout objCount :=
  let ea             := effectiveAlign s.align
  let pageEaddr      := alignDown s.eaddr.val ea
  let pageEnd        := alignUp (s.eaddr.val + s.memsz.val) ea
  let pageLength     := pageEnd - pageEaddr
  let pageInset      := s.eaddr.val - pageEaddr
  let fileOverlayLen := alignUp (pageInset + s.filesz.val) ea
  let fileOffset     := alignDown s.offset.val ea
  let partialBssLen  := fileOverlayLen - (pageInset + s.filesz.val)
  let prot : UInt32 :=
    (if s.perm.read  then (1 : UInt32) else 0) |||
    (if s.perm.write then (2 : UInt32) else 0) |||
    (if s.perm.exec  then (4 : UInt32) else 0)
  { fileSize := fileSize, segment := s, pageEaddr, pageLength, pageInset,
    fileOverlayLen, fileOffset, partialBssLen, prot,
    pageEnd_lt := raw_pageEnd_lt s,
    fileOverlay_le_pageLength := raw_fileOverlay_le_pageLength s,
    vaddr_memsz_le_pageEnd := raw_vaddr_memsz_le_pageEnd s,
    zero_end_le_pageLength := raw_zero_end_le_pageLength s,
    pageInset_eq_vaddr := raw_pageInset_eq_vaddr s,
    relocs }

/-- One past the last byte of the mmap'd range, base-relative. -/
def pageEndAddr (sp : SegmentLayout objCount) : UInt64 := sp.pageEaddr + sp.pageLength

/-- `pageEndAddr.toNat = pageEaddr.toNat + pageLength.toNat` — the
    `pageEnd_lt` invariant rules out wrap. Saves the inline
    `UInt64.toNat_add` + `mod_eq_of_lt` ritual every per-op
    `Finalize` proof would otherwise duplicate. -/
theorem pageEndAddr_toNat (sp : SegmentLayout objCount) :
    sp.pageEndAddr.toNat = sp.pageEaddr.toNat + sp.pageLength.toNat := by
  show (sp.pageEaddr + sp.pageLength).toNat = _
  rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt sp.pageEnd_lt

/-- True when the segment has any file-backed bytes. -/
def hasFileBacked (sp : SegmentLayout objCount) : Bool := sp.fileOverlayLen > 0

/-- True when there are partial-page BSS bytes to zero. -/
def hasPartialBss (sp : SegmentLayout objCount) : Bool := sp.partialBssLen > 0

-- ============================================================================
-- Closed-form projections — `rfl` because each field's stored value is
-- the corresponding `alignDown`/`alignUp` expression. Useful for
-- downstream `simp`-based reasoning.
-- ============================================================================

@[simp] theorem ofSegmentCore_pageEaddr (objCount : Nat) {fileSize : ByteSize}
    (s : Segment fileSize)
    (relocs : Array (Entry objCount s)) :
    (ofSegmentCore objCount s relocs).pageEaddr =
      alignDown s.eaddr.val (effectiveAlign s.align) := rfl

@[simp] theorem ofSegmentCore_pageLength (objCount : Nat) {fileSize : ByteSize}
    (s : Segment fileSize)
    (relocs : Array (Entry objCount s)) :
    (ofSegmentCore objCount s relocs).pageLength =
      alignUp (s.eaddr.val + s.memsz.val) (effectiveAlign s.align) -
      alignDown s.eaddr.val (effectiveAlign s.align) := rfl

@[simp] theorem ofSegmentCore_pageInset (objCount : Nat) {fileSize : ByteSize}
    (s : Segment fileSize)
    (relocs : Array (Entry objCount s)) :
    (ofSegmentCore objCount s relocs).pageInset =
      s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align) := rfl

@[simp] theorem ofSegmentCore_fileOverlayLen (objCount : Nat) {fileSize : ByteSize}
    (s : Segment fileSize)
    (relocs : Array (Entry objCount s)) :
    (ofSegmentCore objCount s relocs).fileOverlayLen =
      alignUp ((s.eaddr.val - alignDown s.eaddr.val (effectiveAlign s.align)) +
               s.filesz.val) (effectiveAlign s.align) := rfl

@[simp] theorem ofSegmentCore_partialBssLen (objCount : Nat) {fileSize : ByteSize}
    (s : Segment fileSize)
    (relocs : Array (Entry objCount s)) :
    (ofSegmentCore objCount s relocs).partialBssLen =
      (ofSegmentCore objCount s relocs).fileOverlayLen -
        ((ofSegmentCore objCount s relocs).pageInset + s.filesz.val) := rfl

@[simp] theorem ofSegmentCore_segment (objCount : Nat) {fileSize : ByteSize}
    (s : Segment fileSize)
    (relocs : Array (Entry objCount s)) :
    (ofSegmentCore objCount s relocs).segment = s := rfl

end SegmentLayout

end ElfLoader.Layout

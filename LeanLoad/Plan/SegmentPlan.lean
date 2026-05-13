/-
Per-segment plan — base-free.

A `SegmentPlan n` lifts one PT_LOAD `Segment` into the loader's view:
page math precomputed once, stored as fields, plus the five
per-segment invariants the materialize-stage safety proofs read by
direct projection (`sp.pageEnd_lt`, `sp.fileOverlay_le_pageLength`, …):

  • `pageEnd_lt`         — `pageVaddr + pageLength < 2^64` (no wrap).
  • `fileOverlay_le_pageLength` — `fileOverlayLen ≤ pageLength`.
  • `vaddr_memsz_le_pageEnd`    — `vaddr + memsz ≤ pageVaddr + pageLength`
                                  (store-window upper bound for relocs).
  • `zero_end_le_pageLength`    — `pageInset + filesz + partialBssLen ≤
                                   pageLength` (BSS-zero slot upper bound).
  • `pageInset_eq_vaddr` — `pageVaddr + pageInset = vaddr` (lets
                           per-slot proofs rewrite to canonical form).

Also carries `relocs : Array (RelocEntry n segment)` — the per-segment
planned relocations; every offset is base-free (relative to base = 0)
and the materializer adds the chosen base when emitting structured slots.

`ofSegmentCore` is the only constructor; it discharges all five
invariant fields at construction via the raw helper lemmas in this
file (`raw_pageEnd_lt`, `raw_fileOverlay_le_pageLength`, …).

Spec: gabi 07 § Program Header (page-aligned mmap views).
-/

import LeanLoad.Plan.Align
import LeanLoad.Plan.Reloc
import LeanLoad.Plan.Resolve
import LeanLoad.Elaborate.Segment
import LeanLoad.Elaborate.Elf
import LeanLoad.Parse.Structs

namespace LeanLoad.Plan

open LeanLoad
open LeanLoad.Parse
open LeanLoad.Elaborate (Elf Segment)
open LeanLoad.Plan.Reloc (RelocEntry)

-- ============================================================================
-- Raw page-arithmetic helpers — about `Segment` + alignDown/alignUp
-- expressions, no `SegmentPlan` reference. Used by `SegmentPlan.ofSegmentCore`
-- to discharge each per-segment invariant field.
-- ============================================================================

namespace SegmentPlan

/-- `vaddr + memsz` doesn't wrap, given `Segment.addrBound`. -/
private theorem vaddr_add_memsz_toNat (s : Segment) :
    (s.vaddr + s.memsz).toNat = s.vaddr.toNat + s.memsz.toNat := by
  have h_2_48 : (2:Nat)^48 < 2^64 := by decide
  have h_no_wrap : s.vaddr.toNat + s.memsz.toNat < 2 ^ 64 := by
    have := s.addrBound; omega
  rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_no_wrap

/-- `effectiveAlign align ≤ align + 1` (toNat). -/
theorem effectiveAlign_le_succ (align : UInt64) :
    (effectiveAlign align).toNat ≤ align.toNat + 1 := by
  unfold effectiveAlign
  split <;> rename_i h
  · have h_eq : align = 0 := by simpa using h
    rw [h_eq]; decide
  · omega

/-- `alignDown s.vaddr ea ≤ alignUp (s.vaddr + s.memsz) ea` —
    page-aligned start ≤ page-aligned end. Prerequisite for
    `pageLength`'s subtraction to be well-defined. -/
private theorem pageVaddr_le_pageEnd_raw (s : Segment) :
    alignDown s.vaddr (effectiveAlign s.align) ≤
    alignUp (s.vaddr + s.memsz) (effectiveAlign s.align) := by
  have h_ea_ne : effectiveAlign s.align ≠ 0 :=
    effectiveAlign_ne_zero s.align
  have h1 := alignDown_le s.vaddr (effectiveAlign s.align)
  have h2 : s.vaddr ≤ s.vaddr + s.memsz := by
    rw [UInt64.le_iff_toNat_le, vaddr_add_memsz_toNat]; omega
  have h_au_no_wrap : (s.vaddr + s.memsz).toNat +
      (effectiveAlign s.align).toNat < 2 ^ 64 := by
    rw [vaddr_add_memsz_toNat]; exact ea_no_wrap _ _ _ s.addrBound
  have h3 : s.vaddr + s.memsz ≤
      alignUp (s.vaddr + s.memsz) (effectiveAlign s.align) :=
    alignUp_ge _ _ h_ea_ne h_au_no_wrap
  rw [UInt64.le_iff_toNat_le] at h1 h2 h3 ⊢
  omega

/-- `(alignUp (s.vaddr + s.memsz) ea).toNat ≤ s.vaddr + s.memsz + ea`.
    Exposed for `Plan.Layout`'s `ElfPlan.ofElf` proof. -/
theorem alignUp_vm_le (s : Segment) :
    (alignUp (s.vaddr + s.memsz) (effectiveAlign s.align)).toNat ≤
    s.vaddr.toNat + s.memsz.toNat + (effectiveAlign s.align).toNat := by
  have h_ea_ne : effectiveAlign s.align ≠ 0 := effectiveAlign_ne_zero s.align
  have h_au_no_wrap : (s.vaddr + s.memsz).toNat +
      (effectiveAlign s.align).toNat < 2 ^ 64 := by
    rw [vaddr_add_memsz_toNat]; exact ea_no_wrap _ _ _ s.addrBound
  have h_au_le := alignUp_le_add_align _ _ h_ea_ne h_au_no_wrap
  rw [vaddr_add_memsz_toNat] at h_au_le
  exact h_au_le

/-- `(alignUp (s.vaddr + s.memsz) ea).toNat < 2^64`. -/
private theorem alignUp_vm_lt (s : Segment) :
    (alignUp (s.vaddr + s.memsz) (effectiveAlign s.align)).toNat < 2 ^ 64 := by
  have h := alignUp_vm_le s
  have h_no_wrap : s.vaddr.toNat + s.memsz.toNat +
      (effectiveAlign s.align).toNat < 2 ^ 64 := ea_no_wrap _ _ _ s.addrBound
  omega

/-- `s.vaddr + s.memsz ≤ alignUp (s.vaddr + s.memsz) ea` (toNat). -/
private theorem vm_le_alignUp_vm (s : Segment) :
    s.vaddr.toNat + s.memsz.toNat ≤
    (alignUp (s.vaddr + s.memsz) (effectiveAlign s.align)).toNat := by
  rw [← vaddr_add_memsz_toNat]
  apply UInt64.le_iff_toNat_le.mp
  have h_ea_ne : effectiveAlign s.align ≠ 0 := effectiveAlign_ne_zero s.align
  have h_no_wrap : (s.vaddr + s.memsz).toNat +
      (effectiveAlign s.align).toNat < 2 ^ 64 := by
    rw [vaddr_add_memsz_toNat]; exact ea_no_wrap _ _ _ s.addrBound
  exact alignUp_ge _ _ h_ea_ne h_no_wrap

/-- The `pageEnd - pageVaddr` UInt64 subtraction equals the Nat-level
    difference `pageEnd.toNat - pageVaddr.toNat`.
    Exposed for `Plan.Layout`'s `ElfPlan.ofElf` proof. -/
theorem pageLength_toNat (s : Segment) :
    (alignUp (s.vaddr + s.memsz) (effectiveAlign s.align) -
      alignDown s.vaddr (effectiveAlign s.align)).toNat =
    (alignUp (s.vaddr + s.memsz) (effectiveAlign s.align)).toNat -
    (alignDown s.vaddr (effectiveAlign s.align)).toNat :=
  UInt64.toNat_sub_of_le _ _ (pageVaddr_le_pageEnd_raw s)

/-- `pageVaddr + pageLength = pageEnd` (in `Nat`). -/
private theorem pageVaddr_add_pageLength_raw (s : Segment) :
    (alignDown s.vaddr (effectiveAlign s.align)).toNat +
    (alignUp (s.vaddr + s.memsz) (effectiveAlign s.align) -
      alignDown s.vaddr (effectiveAlign s.align)).toNat =
    (alignUp (s.vaddr + s.memsz) (effectiveAlign s.align)).toNat := by
  rw [pageLength_toNat]
  have := UInt64.le_iff_toNat_le.mp (pageVaddr_le_pageEnd_raw s)
  omega

/-- The `pageVaddr + pageLength < 2^64` bound — used as
    `SegmentPlan.pageEnd_lt`. -/
private theorem raw_pageEnd_lt (s : Segment) :
    (alignDown s.vaddr (effectiveAlign s.align)).toNat +
    (alignUp (s.vaddr + s.memsz) (effectiveAlign s.align) -
      alignDown s.vaddr (effectiveAlign s.align)).toNat < 2 ^ 64 := by
  rw [pageVaddr_add_pageLength_raw]; exact alignUp_vm_lt s

/-- The `vaddr + memsz ≤ pageVaddr + pageLength` bound — used as
    `SegmentPlan.vaddr_memsz_le_pageEnd`. -/
private theorem raw_vaddr_memsz_le_pageEnd (s : Segment) :
    s.vaddr.toNat + s.memsz.toNat ≤
    (alignDown s.vaddr (effectiveAlign s.align)).toNat +
    (alignUp (s.vaddr + s.memsz) (effectiveAlign s.align) -
      alignDown s.vaddr (effectiveAlign s.align)).toNat := by
  rw [pageVaddr_add_pageLength_raw]; exact vm_le_alignUp_vm s

/-- The `pageVaddr + pageInset = vaddr` equality — used as
    `SegmentPlan.pageInset_eq_vaddr`. -/
private theorem raw_pageInset_eq_vaddr (s : Segment) :
    (alignDown s.vaddr (effectiveAlign s.align)).toNat +
    (s.vaddr - alignDown s.vaddr (effectiveAlign s.align)).toNat =
    s.vaddr.toNat := by
  have h_ad_le : alignDown s.vaddr (effectiveAlign s.align) ≤ s.vaddr :=
    alignDown_le _ _
  have h_pi_eq : (s.vaddr - alignDown s.vaddr (effectiveAlign s.align)).toNat =
                 s.vaddr.toNat - (alignDown s.vaddr (effectiveAlign s.align)).toNat :=
    UInt64.toNat_sub_of_le _ _ h_ad_le
  rw [h_pi_eq]
  have := UInt64.le_iff_toNat_le.mp h_ad_le
  omega

/-- `pageVaddr + fileOverlayLen ≤ pageVaddr + pageLength` (in `Nat`). -/
private theorem pageVaddr_add_fileOverlayLen_le_pageEnd (s : Segment) :
    (alignDown s.vaddr (effectiveAlign s.align)).toNat +
    (alignUp ((s.vaddr - alignDown s.vaddr (effectiveAlign s.align)) +
              s.filesz) (effectiveAlign s.align)).toNat ≤
    (alignDown s.vaddr (effectiveAlign s.align)).toNat +
    (alignUp (s.vaddr + s.memsz) (effectiveAlign s.align) -
      alignDown s.vaddr (effectiveAlign s.align)).toNat := by
  rw [pageVaddr_add_pageLength_raw]
  have h_ea_ne : effectiveAlign s.align ≠ 0 := effectiveAlign_ne_zero s.align
  have h_filesz_le_memsz : s.filesz.toNat ≤ s.memsz.toNat :=
    UInt64.le_iff_toNat_le.mp s.fileszLeMemsz
  have h_addr := s.addrBound
  have h_ea_le := effectiveAlign_le_succ s.align
  have h_2_48 : (2:Nat)^48 < 2^64 := by decide
  have h_ad_le_v : (alignDown s.vaddr (effectiveAlign s.align)).toNat ≤ s.vaddr.toNat :=
    UInt64.le_iff_toNat_le.mp (alignDown_le _ _)
  have h_pi_eq : (s.vaddr - alignDown s.vaddr (effectiveAlign s.align)).toNat =
                 s.vaddr.toNat - (alignDown s.vaddr (effectiveAlign s.align)).toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (alignDown_le _ _)]
  have h_py_no_wrap : (s.vaddr - alignDown s.vaddr (effectiveAlign s.align)).toNat +
      s.filesz.toNat < 2 ^ 64 := by rw [h_pi_eq]; omega
  have h_py_eq : ((s.vaddr - alignDown s.vaddr (effectiveAlign s.align)) + s.filesz).toNat =
                 (s.vaddr - alignDown s.vaddr (effectiveAlign s.align)).toNat +
                 s.filesz.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_py_no_wrap
  have h_y_no_wrap :
      ((s.vaddr - alignDown s.vaddr (effectiveAlign s.align)) + s.filesz).toNat +
      (effectiveAlign s.align).toNat < 2 ^ 64 := by
    rw [h_py_eq, h_pi_eq]; omega
  have h_sum_no_wrap : s.vaddr.toNat +
      ((s.vaddr - alignDown s.vaddr (effectiveAlign s.align)) + s.filesz).toNat +
      (effectiveAlign s.align).toNat < 2 ^ 64 := by
    rw [h_py_eq, h_pi_eq]; omega
  rw [alignDown_add_alignUp_toNat _ _ _ h_ea_ne h_y_no_wrap h_sum_no_wrap]
  have h_vf_no_wrap : s.vaddr.toNat + s.filesz.toNat < 2 ^ 64 := by omega
  have h_combined :
      alignDown s.vaddr (effectiveAlign s.align) +
      ((s.vaddr - alignDown s.vaddr (effectiveAlign s.align)) + s.filesz) =
      s.vaddr + s.filesz := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, h_py_eq, h_pi_eq, UInt64.toNat_add]
    have h_inner_no_wrap : (alignDown s.vaddr (effectiveAlign s.align)).toNat +
        ((s.vaddr.toNat - (alignDown s.vaddr (effectiveAlign s.align)).toNat) +
         s.filesz.toNat) < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt h_inner_no_wrap, Nat.mod_eq_of_lt h_vf_no_wrap]
    omega
  rw [h_combined]
  have h_vf_eq : (s.vaddr + s.filesz).toNat = s.vaddr.toNat + s.filesz.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_vf_no_wrap
  have h_vm_eq : (s.vaddr + s.memsz).toNat = s.vaddr.toNat + s.memsz.toNat :=
    vaddr_add_memsz_toNat s
  apply alignUp_mono_toNat _ _ _ h_ea_ne
  · rw [h_vf_eq]; omega
  · rw [h_vm_eq]; exact ea_no_wrap _ _ _ s.addrBound
  · rw [h_vf_eq, h_vm_eq]; omega

/-- The `fileOverlayLen ≤ pageLength` bound — used as
    `SegmentPlan.fileOverlay_le_pageLength`. -/
private theorem raw_fileOverlay_le_pageLength (s : Segment) :
    (alignUp ((s.vaddr - alignDown s.vaddr (effectiveAlign s.align)) +
              s.filesz) (effectiveAlign s.align)).toNat ≤
    (alignUp (s.vaddr + s.memsz) (effectiveAlign s.align) -
      alignDown s.vaddr (effectiveAlign s.align)).toNat := by
  have h := pageVaddr_add_fileOverlayLen_le_pageEnd s
  omega

/-- The `pageInset + filesz + partialBssLen ≤ pageLength` bound —
    used as `SegmentPlan.zero_end_le_pageLength`. -/
private theorem raw_zero_end_le_pageLength (s : Segment) :
    (s.vaddr - alignDown s.vaddr (effectiveAlign s.align)).toNat +
    s.filesz.toNat +
    (alignUp ((s.vaddr - alignDown s.vaddr (effectiveAlign s.align)) +
              s.filesz) (effectiveAlign s.align) -
      ((s.vaddr - alignDown s.vaddr (effectiveAlign s.align)) + s.filesz)).toNat ≤
    (alignUp (s.vaddr + s.memsz) (effectiveAlign s.align) -
      alignDown s.vaddr (effectiveAlign s.align)).toNat := by
  -- partialBssLen = fileOverlayLen - (pageInset + filesz) in UInt64.
  -- We show pageInset + filesz ≤ fileOverlayLen (from `alignUp_ge`), so
  -- pageInset + filesz + partialBssLen = fileOverlayLen ≤ pageLength.
  have h_ea_ne : effectiveAlign s.align ≠ 0 := effectiveAlign_ne_zero s.align
  have h_pi_eq : (s.vaddr - alignDown s.vaddr (effectiveAlign s.align)).toNat =
                 s.vaddr.toNat -
                 (alignDown s.vaddr (effectiveAlign s.align)).toNat :=
    UInt64.toNat_sub_of_le _ _ (alignDown_le _ _)
  have h_ad_le : (alignDown s.vaddr (effectiveAlign s.align)).toNat ≤
                 s.vaddr.toNat :=
    UInt64.le_iff_toNat_le.mp (alignDown_le _ _)
  have h_fm := UInt64.le_iff_toNat_le.mp s.fileszLeMemsz
  have h_addr := s.addrBound
  have h_ea_le_succ := effectiveAlign_le_succ s.align
  have h_2_48 : (2:Nat)^48 < 2^64 := by decide
  have h_pi_filesz_no_wrap :
      (s.vaddr - alignDown s.vaddr (effectiveAlign s.align)).toNat +
      s.filesz.toNat < 2 ^ 64 := by
    rw [h_pi_eq]; omega
  have h_pi_filesz_eq :
      ((s.vaddr - alignDown s.vaddr (effectiveAlign s.align)) + s.filesz).toNat =
      (s.vaddr - alignDown s.vaddr (effectiveAlign s.align)).toNat +
      s.filesz.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_pi_filesz_no_wrap
  have h_y_no_wrap :
      ((s.vaddr - alignDown s.vaddr (effectiveAlign s.align)) + s.filesz).toNat +
      (effectiveAlign s.align).toNat < 2 ^ 64 := by
    rw [h_pi_filesz_eq, h_pi_eq]; omega
  have h_pi_filesz_le_fol :
      ((s.vaddr - alignDown s.vaddr (effectiveAlign s.align)) + s.filesz).toNat ≤
      (alignUp ((s.vaddr - alignDown s.vaddr (effectiveAlign s.align)) +
                s.filesz) (effectiveAlign s.align)).toNat :=
    UInt64.le_iff_toNat_le.mp (alignUp_ge _ _ h_ea_ne h_y_no_wrap)
  have h_partial_eq :
      (alignUp ((s.vaddr - alignDown s.vaddr (effectiveAlign s.align)) +
                s.filesz) (effectiveAlign s.align) -
        ((s.vaddr - alignDown s.vaddr (effectiveAlign s.align)) +
          s.filesz)).toNat =
      (alignUp ((s.vaddr - alignDown s.vaddr (effectiveAlign s.align)) +
                s.filesz) (effectiveAlign s.align)).toNat -
      ((s.vaddr - alignDown s.vaddr (effectiveAlign s.align)) + s.filesz).toNat :=
    UInt64.toNat_sub_of_le _ _
      (UInt64.le_iff_toNat_le.mpr h_pi_filesz_le_fol)
  have h_fo_le_pl := raw_fileOverlay_le_pageLength s
  rw [h_partial_eq, h_pi_filesz_eq]
  omega

end SegmentPlan

-- ============================================================================
-- SegmentPlan n — one PT_LOAD with page math + per-segment invariants
-- + per-segment relocs. Base-free: every offset is relative to base = 0.
-- ============================================================================

/-- A `Segment` lifted to the loader's view. All page math is
    precomputed once via `ofSegmentCore`; addresses are relative to
    `base = 0`. Per-segment invariants live as Prop fields so consumers
    project them directly (`sp.pageEnd_lt`) — there is no
    `∀ j, ∀ h : j < segs.size, …` quantifier on `ElfPlan` to peel.

    `relocs` is the per-segment planned-relocation array (built parallel
    to construction in `Plan.Layout.ofElf`). -/
structure SegmentPlan (n : Nat) where
  /-- Underlying gabi segment. Carries `rela`/`jmprel` for reloc
      planning and the `addrBound` invariant for proofs. -/
  segment        : Segment
  /-- `alignDown vaddr ea` — page-aligned start. -/
  pageVaddr      : UInt64
  /-- Total page-aligned mmap length. -/
  pageLength     : UInt64
  /-- `vaddr − pageVaddr`. Distance from page start to first useful byte. -/
  pageInset      : UInt64
  /-- Page-aligned length of the file-backed overlay. Zero when `filesz = 0`. -/
  fileOverlayLen : UInt64
  /-- Page-aligned file offset for the overlay's `mmap(2)`. -/
  fileOffset     : UInt64
  /-- Bytes from `filesz` to the overlay's page-aligned end —
      file-mapped (not zero-guaranteed), explicitly zeroed via the
      per-segment `Zero` slot. -/
  partialBssLen  : UInt64
  /-- POSIX `PROT_*` bits derived from gabi `PF_*`. -/
  prot           : UInt32
  /-- `pageVaddr + pageLength < 2^64` — the materialize-stage UInt64
      addition lifts to `Nat` without wrap. -/
  pageEnd_lt : pageVaddr.toNat + pageLength.toNat < 2 ^ 64
  /-- The file overlay sits inside the page-aligned segment range —
      the `SegmentSafe.mmapInRange` bound. -/
  fileOverlay_le_pageLength : fileOverlayLen.toNat ≤ pageLength.toNat
  /-- The 4/8-byte write window of any rela sits inside the
      page-aligned segment range — combines with `coversRela` to
      discharge `SegmentSafe.storesInRange`. -/
  vaddr_memsz_le_pageEnd : segment.vaddr.toNat + segment.memsz.toNat ≤
    pageVaddr.toNat + pageLength.toNat
  /-- The partial-page BSS zero slot's end sits inside the
      page-aligned segment range — the `SegmentSafe.zeroInRange`
      bound. -/
  zero_end_le_pageLength : pageInset.toNat + segment.filesz.toNat +
    partialBssLen.toNat ≤ pageLength.toNat
  /-- The zero slot starts at `pageVaddr + pageInset = vaddr`. Lets
      the zero slot's absolute address simplify to `base + vaddr +
      filesz` for proofs. -/
  pageInset_eq_vaddr : pageVaddr.toNat + pageInset.toNat = segment.vaddr.toNat
  /-- Planned relocations targeting this segment, in `seg.rela ++
      seg.jmprel` order. Each entry carries its `coversRela` witness
      keyed to `segment` so `SegmentSafe.storesInRange` is
      structurally provable. `Materialize.bakeSegmentRelocs` reads
      this directly. -/
  relocs         : Array (RelocEntry n segment)

namespace SegmentPlan

/-- Compute the page-math view of a `Segment` and discharge each
    per-segment invariant. Callers supply `relocs` separately
    (typically via `Reloc.planSegment`). -/
def ofSegmentCore (n : Nat) (s : Segment) (relocs : Array (RelocEntry n s)) :
    SegmentPlan n :=
  let ea             := effectiveAlign s.align
  let pageVaddr      := alignDown s.vaddr ea
  let pageEnd        := alignUp (s.vaddr + s.memsz) ea
  let pageLength     := pageEnd - pageVaddr
  let pageInset      := s.vaddr - pageVaddr
  let fileOverlayLen := alignUp (pageInset + s.filesz) ea
  let fileOffset     := alignDown s.offset ea
  let partialBssLen  := fileOverlayLen - (pageInset + s.filesz)
  let prot : UInt32 :=
    (if s.perm.read  then (1 : UInt32) else 0) |||
    (if s.perm.write then (2 : UInt32) else 0) |||
    (if s.perm.exec  then (4 : UInt32) else 0)
  { segment := s, pageVaddr, pageLength, pageInset,
    fileOverlayLen, fileOffset, partialBssLen, prot,
    pageEnd_lt := raw_pageEnd_lt s,
    fileOverlay_le_pageLength := raw_fileOverlay_le_pageLength s,
    vaddr_memsz_le_pageEnd := raw_vaddr_memsz_le_pageEnd s,
    zero_end_le_pageLength := raw_zero_end_le_pageLength s,
    pageInset_eq_vaddr := raw_pageInset_eq_vaddr s,
    relocs }

/-- Compute the loader view of a `Segment`, planning its relocations
    against the global elf array. -/
def ofSegment (elfs : Array Elf) (rt : Resolve.Table elfs.size)
    (objectIdx : Fin elfs.size) (s : Segment) : SegmentPlan elfs.size :=
  ofSegmentCore elfs.size s (Reloc.planSegment elfs rt objectIdx s)

/-- One past the last byte of the mmap'd range, base-relative. -/
def pageEndAddr (sp : SegmentPlan n) : UInt64 := sp.pageVaddr + sp.pageLength

/-- `pageEndAddr.toNat = pageVaddr.toNat + pageLength.toNat` — the
    `pageEnd_lt` invariant rules out wrap. Saves the inline
    `UInt64.toNat_add` + `mod_eq_of_lt` ritual every per-slot
    `Materialize` proof would otherwise duplicate. -/
theorem pageEndAddr_toNat (sp : SegmentPlan n) :
    sp.pageEndAddr.toNat = sp.pageVaddr.toNat + sp.pageLength.toNat := by
  show (sp.pageVaddr + sp.pageLength).toNat = _
  rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt sp.pageEnd_lt

/-- True when the segment has any file-backed bytes. -/
def hasFileBacked (sp : SegmentPlan n) : Bool := sp.fileOverlayLen > 0

/-- True when there are partial-page BSS bytes to zero. -/
def hasPartialBss (sp : SegmentPlan n) : Bool := sp.partialBssLen > 0

-- ============================================================================
-- Closed-form projections — `rfl` because each field's stored value is
-- the corresponding `alignDown`/`alignUp` expression. Useful for
-- downstream `simp`-based reasoning.
-- ============================================================================

@[simp] theorem ofSegmentCore_pageVaddr (n : Nat) (s : Segment)
    (relocs : Array (RelocEntry n s)) :
    (ofSegmentCore n s relocs).pageVaddr =
      alignDown s.vaddr (effectiveAlign s.align) := rfl

@[simp] theorem ofSegmentCore_pageLength (n : Nat) (s : Segment)
    (relocs : Array (RelocEntry n s)) :
    (ofSegmentCore n s relocs).pageLength =
      alignUp (s.vaddr + s.memsz) (effectiveAlign s.align) -
      alignDown s.vaddr (effectiveAlign s.align) := rfl

@[simp] theorem ofSegmentCore_pageInset (n : Nat) (s : Segment)
    (relocs : Array (RelocEntry n s)) :
    (ofSegmentCore n s relocs).pageInset =
      s.vaddr - alignDown s.vaddr (effectiveAlign s.align) := rfl

@[simp] theorem ofSegmentCore_fileOverlayLen (n : Nat) (s : Segment)
    (relocs : Array (RelocEntry n s)) :
    (ofSegmentCore n s relocs).fileOverlayLen =
      alignUp ((s.vaddr - alignDown s.vaddr (effectiveAlign s.align)) +
               s.filesz) (effectiveAlign s.align) := rfl

@[simp] theorem ofSegmentCore_partialBssLen (n : Nat) (s : Segment)
    (relocs : Array (RelocEntry n s)) :
    (ofSegmentCore n s relocs).partialBssLen =
      (ofSegmentCore n s relocs).fileOverlayLen -
      ((ofSegmentCore n s relocs).pageInset + s.filesz) := rfl

@[simp] theorem ofSegmentCore_segment (n : Nat) (s : Segment)
    (relocs : Array (RelocEntry n s)) :
    (ofSegmentCore n s relocs).segment = s := rfl

end SegmentPlan

end LeanLoad.Plan

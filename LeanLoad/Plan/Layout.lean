/-
Layout planning — base-free.

Each PT_LOAD `Segment` lifts to a `SegmentPlan n` whose page math is
precomputed once and stored: `pageVaddr`, `pageLength`, `pageInset`,
`fileOverlayLen`, `fileOffset`, `partialBssLen`, `prot`. The plan
also carries its own `relocs : Array (RelocEntry n)` — there is no
parallel relocation tree. Every offset is relative to `base = 0`;
the materializer adds the chosen base when emitting structured slots.

Hierarchy:
  • `SegmentPlan n` — one PT_LOAD with page math + per-segment relocs.
  • `ElfPlan n`     — one elf's `SegmentPlan`s, its `advance`, plus a
                      proof that the page-aligned ranges don't overlap
                      (`segmentsSorted`) and each one fits in `advance`.
  • `LoadPlan n`    — every elf's `ElfPlan` plus the cumulative
                      `totalSpan` (the `len` for `mmapAnonAlloc`).

The natural number parameter `n` is the elf count: every `RelocEntry`
indexes the global elf array with `Fin n`.

`LoadPlan.ofElfs` builds the whole tree in one pass: it consumes
`(elfs, resolveTable)` and produces a fully-planned `LoadPlan elfs.size`.
Per-elf page-aligned non-overlap is validated as part of construction
— failure is rare (modern toolchains never emit overlapping page
ranges) but possible in principle.

Once a `LoadPlan` exists, `assignBases base lp` is total: it stacks
each elf by `alignUp objectSpan 0x1000` from the IO-supplied base.

Spec: gabi 07 § Program Header (page-aligned mmap views, base
assignment, span over loadable segments).
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
open LeanLoad.Reloc (RelocEntry)

-- ============================================================================
-- SegmentPlan n — one PT_LOAD with page math + per-segment relocs.
-- Base-free: every offset is relative to base = 0.
-- ============================================================================

/-- A `Segment` lifted to the loader's view. All page math is
    precomputed once via `ofSegment`; addresses are relative to
    `base = 0`. The materializer adds the chosen base when emitting
    the per-segment structured slots. `relocs` is the per-segment
    planned-relocation array (built parallel to construction in
    `Plan.Layout.ofElf`). -/
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
  /-- Planned relocations targeting this segment, in `seg.rela ++
      seg.jmprel` order. `Materialize.bakeSegmentRelocs` reads this
      directly. -/
  relocs         : Array (RelocEntry n)

namespace SegmentPlan

/-- Compute the page-math view of a `Segment` without filling in
    relocs. Callers supply `relocs` separately (typically via
    `Reloc.planSegment`). -/
def ofSegmentCore (n : Nat) (s : Segment) (relocs : Array (RelocEntry n)) :
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
    fileOverlayLen, fileOffset, partialBssLen, prot, relocs }

/-- Compute the loader view of a `Segment`, planning its relocations
    against the global elf array. -/
def ofSegment (elfs : Array Elf) (rt : Resolve.Table elfs.size)
    (objectIdx : Fin elfs.size) (s : Segment) : SegmentPlan elfs.size :=
  ofSegmentCore elfs.size s (Reloc.planSegment elfs rt objectIdx s)

/-- One past the last byte of the mmap'd range, base-relative. -/
def pageEndAddr (sp : SegmentPlan n) : UInt64 := sp.pageVaddr + sp.pageLength

/-- True when the segment has any file-backed bytes. -/
def hasFileBacked (sp : SegmentPlan n) : Bool := sp.fileOverlayLen > 0

/-- True when there are partial-page BSS bytes to zero. -/
def hasPartialBss (sp : SegmentPlan n) : Bool := sp.partialBssLen > 0

/-- `vaddr + memsz` doesn't wrap, given `Segment.addrBound`. -/
private theorem vaddr_add_memsz_toNat (s : Segment) :
    (s.vaddr + s.memsz).toNat = s.vaddr.toNat + s.memsz.toNat := by
  have h_2_48 : (2:Nat)^48 < 2^64 := by decide
  have h_no_wrap : s.vaddr.toNat + s.memsz.toNat < 2 ^ 64 := by
    have := s.addrBound; omega
  rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_no_wrap

/-- Projection: the stored `pageVaddr` is exactly `alignDown vaddr ea`. -/
@[simp] theorem ofSegmentCore_pageVaddr (n : Nat) (s : Segment)
    (relocs : Array (RelocEntry n)) :
    (ofSegmentCore n s relocs).pageVaddr =
      alignDown s.vaddr (effectiveAlign s.align) := rfl

/-- Projection: the stored `pageLength` is `alignUp (vaddr+memsz) ea -
    alignDown vaddr ea`. -/
@[simp] theorem ofSegmentCore_pageLength (n : Nat) (s : Segment)
    (relocs : Array (RelocEntry n)) :
    (ofSegmentCore n s relocs).pageLength =
      alignUp (s.vaddr + s.memsz) (effectiveAlign s.align) -
      alignDown s.vaddr (effectiveAlign s.align) := rfl

/-- Projection: the stored `pageInset` is `vaddr - alignDown vaddr ea`. -/
@[simp] theorem ofSegmentCore_pageInset (n : Nat) (s : Segment)
    (relocs : Array (RelocEntry n)) :
    (ofSegmentCore n s relocs).pageInset =
      s.vaddr - alignDown s.vaddr (effectiveAlign s.align) := rfl

/-- Projection: the stored `fileOverlayLen` is `alignUp (pageInset+filesz) ea`. -/
@[simp] theorem ofSegmentCore_fileOverlayLen (n : Nat) (s : Segment)
    (relocs : Array (RelocEntry n)) :
    (ofSegmentCore n s relocs).fileOverlayLen =
      alignUp ((s.vaddr - alignDown s.vaddr (effectiveAlign s.align)) +
               s.filesz) (effectiveAlign s.align) := rfl

/-- Projection: the stored `partialBssLen` is `fileOverlayLen -
    (pageInset + filesz)`. -/
@[simp] theorem ofSegmentCore_partialBssLen (n : Nat) (s : Segment)
    (relocs : Array (RelocEntry n)) :
    (ofSegmentCore n s relocs).partialBssLen =
      (ofSegmentCore n s relocs).fileOverlayLen -
      ((ofSegmentCore n s relocs).pageInset + s.filesz) := rfl

/-- Projection: the stored `segment` is `s` itself. -/
@[simp] theorem ofSegmentCore_segment (n : Nat) (s : Segment)
    (relocs : Array (RelocEntry n)) :
    (ofSegmentCore n s relocs).segment = s := rfl

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

/-- `pageEndAddr.toNat = (alignUp (vaddr + memsz) ea).toNat`. -/
theorem ofSegmentCore_pageEndAddr_toNat (n : Nat) (s : Segment)
    (relocs : Array (RelocEntry n)) :
    (ofSegmentCore n s relocs).pageEndAddr.toNat =
    (alignUp (s.vaddr + s.memsz) (effectiveAlign s.align)).toNat := by
  show ((ofSegmentCore n s relocs).pageVaddr +
        (ofSegmentCore n s relocs).pageLength).toNat = _
  rw [ofSegmentCore_pageVaddr, ofSegmentCore_pageLength]
  have h_pv_le := pageVaddr_le_pageEnd_raw s
  rw [UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ h_pv_le]
  have h_pv_le_nat := UInt64.le_iff_toNat_le.mp h_pv_le
  have h_au_lt : (alignUp (s.vaddr + s.memsz) (effectiveAlign s.align)).toNat < 2^64 :=
    (alignUp _ _).toNat_lt_size
  rw [show (alignDown s.vaddr (effectiveAlign s.align)).toNat +
          ((alignUp (s.vaddr + s.memsz) (effectiveAlign s.align)).toNat -
           (alignDown s.vaddr (effectiveAlign s.align)).toNat) =
          (alignUp (s.vaddr + s.memsz) (effectiveAlign s.align)).toNat from by omega]
  exact Nat.mod_eq_of_lt h_au_lt

/-- `pageEndAddr.toNat ≤ vaddr + memsz + ea` — key upper bound. -/
theorem ofSegmentCore_pageEndAddr_le (n : Nat) (s : Segment)
    (relocs : Array (RelocEntry n)) :
    (ofSegmentCore n s relocs).pageEndAddr.toNat ≤
    s.vaddr.toNat + s.memsz.toNat + (effectiveAlign s.align).toNat := by
  rw [ofSegmentCore_pageEndAddr_toNat]
  have h_ea_ne : effectiveAlign s.align ≠ 0 := effectiveAlign_ne_zero s.align
  have h_au_no_wrap : (s.vaddr + s.memsz).toNat +
      (effectiveAlign s.align).toNat < 2 ^ 64 := by
    rw [vaddr_add_memsz_toNat]; exact ea_no_wrap _ _ _ s.addrBound
  have h_au_le := alignUp_le_add_align _ _ h_ea_ne h_au_no_wrap
  rw [vaddr_add_memsz_toNat] at h_au_le
  exact h_au_le

/-- `pageEndAddr.toNat < 2^64` (no wrap). -/
theorem ofSegmentCore_pageEndAddr_lt (n : Nat) (s : Segment)
    (relocs : Array (RelocEntry n)) :
    (ofSegmentCore n s relocs).pageEndAddr.toNat < 2 ^ 64 := by
  have h := ofSegmentCore_pageEndAddr_le n s relocs
  have h_no_wrap : s.vaddr.toNat + s.memsz.toNat +
      (effectiveAlign s.align).toNat < 2 ^ 64 := ea_no_wrap _ _ _ s.addrBound
  omega

/-- `pageVaddr + pageLength = pageEndAddr` (in `Nat`, no wrap). Mprotect bound. -/
theorem ofSegmentCore_pageVaddr_add_pageLength (n : Nat) (s : Segment)
    (relocs : Array (RelocEntry n)) :
    (ofSegmentCore n s relocs).pageVaddr.toNat +
    (ofSegmentCore n s relocs).pageLength.toNat =
    (ofSegmentCore n s relocs).pageEndAddr.toNat := by
  show _ = ((ofSegmentCore n s relocs).pageVaddr +
            (ofSegmentCore n s relocs).pageLength).toNat
  rw [UInt64.toNat_add]
  have h_lt : (ofSegmentCore n s relocs).pageEndAddr.toNat < 2 ^ 64 :=
    ofSegmentCore_pageEndAddr_lt n s relocs
  have h_eq : (ofSegmentCore n s relocs).pageVaddr.toNat +
              (ofSegmentCore n s relocs).pageLength.toNat =
              (ofSegmentCore n s relocs).pageEndAddr.toNat := by
    rw [ofSegmentCore_pageEndAddr_toNat, ofSegmentCore_pageVaddr,
        ofSegmentCore_pageLength]
    have h_pv_le := pageVaddr_le_pageEnd_raw s
    rw [UInt64.toNat_sub_of_le _ _ h_pv_le]
    have := UInt64.le_iff_toNat_le.mp h_pv_le
    omega
  rw [h_eq]
  exact (Nat.mod_eq_of_lt h_lt).symm

/-- `vaddr + memsz ≤ pageEndAddr` (in `Nat`). Store bound. -/
theorem ofSegmentCore_vaddr_add_memsz_le_pageEndAddr (n : Nat) (s : Segment)
    (relocs : Array (RelocEntry n)) :
    s.vaddr.toNat + s.memsz.toNat ≤
    (ofSegmentCore n s relocs).pageEndAddr.toNat := by
  rw [ofSegmentCore_pageEndAddr_toNat, ← vaddr_add_memsz_toNat]
  apply UInt64.le_iff_toNat_le.mp
  have h_ea_ne : effectiveAlign s.align ≠ 0 := effectiveAlign_ne_zero s.align
  have h_no_wrap : (s.vaddr + s.memsz).toNat +
      (effectiveAlign s.align).toNat < 2 ^ 64 := by
    rw [vaddr_add_memsz_toNat]; exact ea_no_wrap _ _ _ s.addrBound
  exact alignUp_ge _ _ h_ea_ne h_no_wrap

/-- `effectiveAlign align ≤ align + 1` (toNat). -/
theorem effectiveAlign_le_succ (align : UInt64) :
    (effectiveAlign align).toNat ≤ align.toNat + 1 := by
  unfold effectiveAlign
  split <;> rename_i h
  · have h_eq : align = 0 := by simpa using h
    rw [h_eq]; decide
  · omega

/-- `pageVaddr + fileOverlayLen ≤ pageEndAddr` (in `Nat`). Mmap/Zero bound. -/
theorem ofSegmentCore_pageVaddr_add_fileOverlayLen_le_pageEndAddr (n : Nat)
    (s : Segment) (relocs : Array (RelocEntry n)) :
    (ofSegmentCore n s relocs).pageVaddr.toNat +
    (ofSegmentCore n s relocs).fileOverlayLen.toNat ≤
    (ofSegmentCore n s relocs).pageEndAddr.toNat := by
  rw [ofSegmentCore_pageVaddr, ofSegmentCore_fileOverlayLen,
      ofSegmentCore_pageEndAddr_toNat]
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

end SegmentPlan

-- ============================================================================
-- UInt64 max helpers — small lemmas the per-elf `pageEndAddr_le_advance`
-- proof needs to reason about `Array.foldl max`.
-- ============================================================================

theorem UInt64.le_max_left (a b : UInt64) : a ≤ max a b := by
  show a ≤ if a ≤ b then b else a
  by_cases h : a ≤ b
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact UInt64.le_refl _

theorem UInt64.le_max_right (a b : UInt64) : b ≤ max a b := by
  show b ≤ if a ≤ b then b else a
  by_cases h : a ≤ b
  · rw [if_pos h]; exact UInt64.le_refl _
  · rw [if_neg h]
    rw [UInt64.le_iff_toNat_le]
    have h_n : ¬ a.toNat ≤ b.toNat := fun hn =>
      h (UInt64.le_iff_toNat_le.mpr hn)
    omega

/-- `(max a b).toNat = max a.toNat b.toNat` for UInt64. Lets `omega`
    reason about UInt64 max via the Nat-side lemmas. -/
theorem UInt64.toNat_max (a b : UInt64) :
    (max a b).toNat = max a.toNat b.toNat := by
  show (if a ≤ b then b else a).toNat = _
  by_cases h : a ≤ b
  · rw [if_pos h]
    have h_n : a.toNat ≤ b.toNat := UInt64.le_iff_toNat_le.mp h
    exact (Nat.max_eq_right h_n).symm
  · rw [if_neg h]
    have h_n : ¬ a.toNat ≤ b.toNat := fun hn =>
      h (UInt64.le_iff_toNat_le.mpr hn)
    have h_le : b.toNat ≤ a.toNat := by omega
    exact (Nat.max_eq_left h_le).symm

/-- Page-aligned segment ranges are sorted: each one's `pageEndAddr`
    is ≤ the next one's `pageVaddr`. Base-free; translation
    invariant. Same shape as `Elaborate.Sorted`, but on the
    page-aligned ranges. -/
def Sorted (segs : Array (SegmentPlan n)) : Prop :=
  ∀ i, ∀ _ : i < segs.size, ∀ j, ∀ _ : j < segs.size,
    i < j → segs[i].pageEndAddr ≤ segs[j].pageVaddr

instance (segs : Array (SegmentPlan n)) : Decidable (Sorted segs) := by
  unfold Sorted; infer_instance

-- ============================================================================
-- ElfPlan n — one elf's SegmentPlans + advance + per-segment bound.
-- ============================================================================

/-- One elf's segment plans, the per-elf cursor advance (page-aligned
    cumulative span), and proofs that
      • the page-aligned ranges don't overlap (`segmentsSorted`),
      • each segment's `pageEndAddr` fits inside `advance`
        (`pageEndAddr_le_advance`) — the per-elf containment bound
        the safety predicates consume.
    Construction (`ofElf`) is fallible: it fails when the page-
    aligned non-overlap validation rejects the elf, or if the
    `advance` computation would wrap UInt64 (impossible on Linux). -/
structure ElfPlan (n : Nat) where
  elf            : Elf
  /-- Parallel to `elf.segments`, lifted to the loader view + relocs. -/
  segments       : Array (SegmentPlan n)
  /-- Per-elf cursor advance: at least `alignUp (max pageEndAddr) 0x1000`,
      possibly more if the no-wrap dance demands. The reservation
      reserves exactly `advance` bytes per elf via `assignBases`. -/
  advance        : UInt64
  /-- Page-aligned segment ranges don't overlap pairwise. -/
  segmentsSorted : Sorted segments
  /-- Each segment's mmap'd range fits in `[0, advance)` (in `Nat`).
      The crux of the per-elf containment bound. -/
  pageEndAddr_le_advance : ∀ (i : Nat) (h : i < segments.size),
    segments[i].pageEndAddr.toNat ≤ advance.toNat

namespace ElfPlan

/-- Build an `ElfPlan n`, validating page-aligned non-overlap.
    `Elaborate.Sorted` and `Elaborate.NonOverlap` are on raw vaddrs;
    after page-rounding, small-alignment edge cases can collapse two
    segments onto the same page (modern toolchains never emit this,
    but it's not statically excluded by gabi-level invariants).

    Reloc planning happens here too: each segment's `relocs` field is
    filled by `Reloc.planSegment`. -/
def ofElf (elfs : Array Elf) (rt : Resolve.Table elfs.size)
    (objectIdx : Fin elfs.size) : Except String (ElfPlan elfs.size) :=
  let e := elfs[objectIdx]
  let segs : Array (SegmentPlan elfs.size) :=
    e.segments.map fun s =>
      SegmentPlan.ofSegmentCore elfs.size s
        (Reloc.planSegment elfs rt objectIdx s)
  if h_sorted : Sorted segs then
    let objectSpan : UInt64 := segs.foldl (init := 0) fun acc sp =>
      max acc sp.pageEndAddr
    let advance := alignUp objectSpan 0x1000
    have h_size_eq : segs.size = e.segments.size := by simp [segs]
    have h_each_pe_lt_2_48 : ∀ (i : Nat) (h : i < segs.size),
        segs[i].pageEndAddr.toNat ≤ 2 ^ 48 := by
      intro i h_lt
      have h_lt_e : i < e.segments.size := h_size_eq ▸ h_lt
      have h_eq : segs[i]'h_lt = SegmentPlan.ofSegmentCore elfs.size
          (e.segments[i]'h_lt_e)
          (Reloc.planSegment elfs rt objectIdx (e.segments[i]'h_lt_e)) := by
        show (e.segments.map _)[i]'h_lt = _
        rw [Array.getElem_map]
      rw [h_eq]
      have h_le := SegmentPlan.ofSegmentCore_pageEndAddr_le elfs.size
        (e.segments[i]'h_lt_e)
        (Reloc.planSegment elfs rt objectIdx (e.segments[i]'h_lt_e))
      have h_addr := (e.segments[i]'h_lt_e).addrBound
      have h_ea := SegmentPlan.effectiveAlign_le_succ (e.segments[i]'h_lt_e).align
      have h_2_48 : (2:Nat)^48 < 2^64 := by decide
      omega
    have h_foldl_lt_2_48 : objectSpan.toNat ≤ 2 ^ 48 := by
      let motive : Nat → UInt64 → Prop := fun _ acc => acc.toNat ≤ 2 ^ 48
      have h_full : motive segs.size objectSpan := by
        show motive segs.size _
        refine Array.foldl_induction motive ?_ ?_
        · show (0 : UInt64).toNat ≤ 2 ^ 48; decide
        · intro idx acc ih
          show (max acc segs[idx.val].pageEndAddr).toNat ≤ 2 ^ 48
          rw [UInt64.toNat_max]
          have h_pe := h_each_pe_lt_2_48 idx.val idx.isLt
          exact Nat.max_le.mpr ⟨ih, h_pe⟩
      exact h_full
    have h_no_wrap : objectSpan.toNat + (0x1000 : UInt64).toNat < 2 ^ 64 := by
      have h_1000 : (0x1000 : UInt64).toNat = 0x1000 := by decide
      have h_2_48_p : (2:Nat)^48 + 0x1000 < 2^64 := by decide
      rw [h_1000]; omega
    have h_align_ne : (0x1000 : UInt64) ≠ 0 := by decide
    have h_obj_le_adv : objectSpan ≤ advance :=
      alignUp_ge _ _ h_align_ne h_no_wrap
    have h_obj_le_adv_n := UInt64.le_iff_toNat_le.mp h_obj_le_adv
    have h_pe_le_obj : ∀ (i : Nat) (h : i < segs.size),
        segs[i].pageEndAddr.toNat ≤ objectSpan.toNat := by
      intro i h_lt
      let motive : Nat → UInt64 → Prop := fun n acc =>
        ∀ (k : Nat) (_ : k < n) (h_size : k < segs.size),
          segs[k].pageEndAddr.toNat ≤ acc.toNat
      have h_full : motive segs.size objectSpan := by
        show motive segs.size _
        refine Array.foldl_induction motive ?_ ?_
        · intro k h_k _; omega
        · intro idx acc ih k h_k h_size
          show segs[k].pageEndAddr.toNat ≤
               (max acc segs[idx.val].pageEndAddr).toNat
          rw [UInt64.toNat_max]
          rcases Nat.lt_or_ge k idx.val with h_k_lt | h_k_ge
          · have h := ih k h_k_lt h_size
            exact Nat.le_trans h (Nat.le_max_left _ _)
          · have h_eq : k = idx.val := by omega
            subst h_eq
            show segs[idx.val].pageEndAddr.toNat ≤
                 max acc.toNat segs[idx.val].pageEndAddr.toNat
            exact Nat.le_max_right _ _
      exact h_full i h_lt h_lt
    have h_bound : ∀ (i : Nat) (h : i < segs.size),
                   segs[i].pageEndAddr.toNat ≤ advance.toNat := by
      intro i h_lt
      have h := h_pe_le_obj i h_lt
      omega
    .ok { elf := e, segments := segs, advance,
          segmentsSorted := h_sorted,
          pageEndAddr_le_advance := h_bound }
  else
    .error "ElfPlan.ofElf: PT_LOAD page-aligned ranges overlap"

end ElfPlan

-- ============================================================================
-- Cumulative offset (free function over `Array (ElfPlan n)`) — sum of
-- `advance.toNat` for `k < n`, in `Nat` to dodge UInt64 wrap. The
-- canonical Nat-side anchor for every safety bound.
-- ============================================================================

/-- Sum of `(elfs[k].advance).toNat` for `k < n`, in `Nat`. -/
def cumOffset (elfs : Array (ElfPlan m)) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    if h : n < elfs.size then
      cumOffset elfs n + (elfs[n].advance).toNat
    else
      cumOffset elfs n

@[simp] theorem cumOffset_zero (elfs : Array (ElfPlan m)) :
    cumOffset elfs 0 = 0 := rfl

theorem cumOffset_succ_of_lt (elfs : Array (ElfPlan m)) {n : Nat}
    (h : n < elfs.size) :
    cumOffset elfs (n + 1) = cumOffset elfs n + (elfs[n].advance).toNat := by
  show (if h : n < elfs.size then _ + _ else _) = _
  rw [dif_pos h]

theorem cumOffset_mono (elfs : Array (ElfPlan m)) {a b : Nat} (h : a ≤ b) :
    cumOffset elfs a ≤ cumOffset elfs b := by
  induction b with
  | zero =>
    have : a = 0 := Nat.le_zero.mp h
    rw [this]
    exact Nat.le_refl _
  | succ k ih =>
    rcases Nat.lt_or_ge a (k + 1) with h_lt | h_ge
    · have h_le : a ≤ k := Nat.lt_succ_iff.mp h_lt
      have ih_le := ih h_le
      show _ ≤ (if _ : k < elfs.size then _ + _ else _)
      split <;> omega
    · have h_eq : a = k + 1 := Nat.le_antisymm h h_ge
      rw [h_eq]
      exact Nat.le_refl _

-- ============================================================================
-- LoadPlan n — every elf's plan + the cumulative reservation span.
-- The `totalSpan_eq` field connects the UInt64 `totalSpan` to the
-- Nat `cumOffset full` so safety proofs can chain via `Nat`
-- arithmetic. The `elfs_size` field ties the elf array length to `n`
-- so consumers can index totally with `Fin n`.
-- ============================================================================

/-- Top-level base-free plan. `totalSpan` is the `len` to pass to
    `Reserve.run` at the IO boundary; `totalSpan_eq` says it equals
    the `cumOffset` Nat sum (no UInt64 wrap during construction).
    `elfs_size` ties the elf array length to `n`. -/
structure LoadPlan (n : Nat) where
  elfs      : Array (ElfPlan n)
  /-- The elf array has exactly `n` entries — every consumer indexes
      totally with `Fin n`. -/
  elfs_size : elfs.size = n
  /-- `Σ alignUp objectSpan 0x1000` — cumulative reservation span. -/
  totalSpan : UInt64
  /-- Connects UInt64 `totalSpan` to the `Nat` cumulative sum.
      Discharged in `ofElfs` by checking the sum fits in UInt64. -/
  totalSpan_eq : totalSpan.toNat = cumOffset elfs elfs.size

namespace LoadPlan

/-- Convenience: `lp.cumOffset n` over the elf array. -/
def cumOffset (lp : LoadPlan n) (k : Nat) : Nat :=
  _root_.LeanLoad.Plan.cumOffset lp.elfs k

/-- Tail-recursive accumulator that lifts each `Elf` through
    `ElfPlan.ofElf` while maintaining `acc.size = i`. -/
private def buildElfPlans (elfs : Array Elf) (rt : Resolve.Table elfs.size)
    (i : Nat) (h : i ≤ elfs.size)
    (acc : { a : Array (ElfPlan elfs.size) // a.size = i }) :
    Except String { a : Array (ElfPlan elfs.size) // a.size = elfs.size } :=
  if heq : i = elfs.size then
    .ok ⟨acc.val, heq ▸ acc.property⟩
  else
    have hi : i < elfs.size := Nat.lt_of_le_of_ne h heq
    match ElfPlan.ofElf elfs rt ⟨i, hi⟩ with
    | .error e => .error e
    | .ok ep =>
      let acc' : { a : Array (ElfPlan elfs.size) // a.size = i + 1 } :=
        ⟨acc.val.push ep, by rw [Array.size_push, acc.property]⟩
      buildElfPlans elfs rt (i + 1) hi acc'
termination_by elfs.size - i

/-- Build the full base-free plan from raw elfs + resolve table. Each
    elf goes through `ElfPlan.ofElf`, which validates page-aligned
    non-overlap and plans each segment's relocations. Computes the
    `Nat` cumulative span and checks it fits in UInt64 so the
    resulting `LoadPlan` carries the `totalSpan_eq` invariant. -/
def ofElfs (elfs : Array Elf) (rt : Resolve.Table elfs.size) :
    Except String (LoadPlan elfs.size) := do
  let elfPlans ← buildElfPlans elfs rt 0 (Nat.zero_le _) ⟨#[], by simp⟩
  let totalNat :=
    _root_.LeanLoad.Plan.cumOffset elfPlans.val elfPlans.val.size
  if h : totalNat < 2 ^ 64 then
    return {
      elfs := elfPlans.val,
      elfs_size := elfPlans.property,
      totalSpan := UInt64.ofNat totalNat,
      totalSpan_eq := by
        show totalNat % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt h }
  else
    .error s!"LoadPlan.ofElfs: cumulative span {totalNat} exceeds UInt64"

end LoadPlan

-- ============================================================================
-- Base assignment via `Array.ofFn` + `cumOffset`. Per-index lemma
-- (`assignBases_at_toNat`) is a one-liner over the closed-form
-- definition.
-- ============================================================================

/-- Stack each elf at `base + cumOffset i`. Total: every `LoadPlan`
    produces a valid bases array of size `n`. -/
def assignBases (base : UInt64) (lp : LoadPlan n) : Array UInt64 :=
  Array.ofFn fun (i : Fin lp.elfs.size) =>
    base + UInt64.ofNat (cumOffset lp.elfs i.val)

theorem assignBases_size (base : UInt64) (lp : LoadPlan n) :
    (assignBases base lp).size = lp.elfs.size := by
  unfold assignBases; simp

/-- The `i`-th base equals `rsvAddr + cumOffset i` in `Nat`, given
    the global no-wrap precondition `rsvAddr.toNat + lp.totalSpan.toNat
    < 2^64` (which `Reserve.noWrap` discharges). Falls out of
    `Array.getElem_ofFn` plus a small ofNat reduction. -/
theorem assignBases_at_toNat (base : UInt64) (lp : LoadPlan n)
    (h_no_wrap : base.toNat + lp.totalSpan.toNat < 2 ^ 64)
    (i : Nat) (h : i < lp.elfs.size) :
    ((assignBases base lp)[i]'(by rw [assignBases_size]; exact h)).toNat =
    base.toNat + cumOffset lp.elfs i := by
  unfold assignBases
  rw [Array.getElem_ofFn]
  have h_cum_le : cumOffset lp.elfs i ≤ cumOffset lp.elfs lp.elfs.size :=
    cumOffset_mono _ (Nat.le_of_lt h)
  have h_total_eq : lp.totalSpan.toNat = cumOffset lp.elfs lp.elfs.size :=
    lp.totalSpan_eq
  have h_cum_lt : cumOffset lp.elfs i < 2 ^ 64 := by omega
  have h_sum_lt : base.toNat + cumOffset lp.elfs i < 2 ^ 64 := by omega
  rw [UInt64.toNat_add]
  show (base.toNat + (cumOffset lp.elfs i) % 2 ^ 64) % 2 ^ 64 =
       base.toNat + cumOffset lp.elfs i
  rw [Nat.mod_eq_of_lt h_cum_lt, Nat.mod_eq_of_lt h_sum_lt]

end LeanLoad.Plan

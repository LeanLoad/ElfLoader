/-
Layout — per-object segment arrangement, pure.

Spec: gabi 07 § Program Header (positional concerns — base
assignment, span over loadable segments, page-aligned mmap views).

After Layout, every absolute address Realize and Apply need is
derivable from a `Region` (Segment + chosen base). Layout.Region is
the loader's view; `Elaborate.Segment` is gabi-only.

`Region` exposes the four mmap-time spans separately:
  - file-backed overlay   → `mmap(handle, ...)` from the open fd
  - partial-page BSS      → existing overlay page bytes that need
                            explicit zeroing (file mapping past EOF
                            isn't guaranteed zero in the partial-page
                            slot — toolchains place arbitrary bytes
                            after `filesz` on the same page)
  - full-page BSS         → fresh anonymous pages past the overlay
  - mprotect target       → final permissions for the whole region

Init/fini ordering lives in `LeanLoad.Plan.Init` (gabi 08).
-/

import LeanLoad.Elaborate.Segment
import LeanLoad.Elaborate.Elf
import LeanLoad.Parse.Structs

namespace LeanLoad.Layout

open LeanLoad
open LeanLoad.Parse
open LeanLoad.Elaborate (Elf Segment)

-- ============================================================================
-- Page-arithmetic helpers — UInt64-saturating align{Down,Up} and the
-- two soundness theorems the per-region proofs consume.
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

/-- Effective alignment: `align`, with `0` lifted to `1` so every
    page-arithmetic def below is total. -/
def effectiveAlign (align : UInt64) : UInt64 :=
  if align == 0 then 1 else align

theorem effectiveAlign_ne_zero (align : UInt64) :
    effectiveAlign align ≠ 0 := by
  unfold effectiveAlign
  split
  · decide
  · intro h; rename_i hne; apply hne; simp [h]

private theorem ea_no_wrap (vaddr memsz align : UInt64)
    (h_addr : vaddr.toNat + memsz.toNat + align.toNat < 2 ^ 48) :
    vaddr.toNat + memsz.toNat + (effectiveAlign align).toNat < 2^64 := by
  have h_2_48 : (2:Nat)^48 + 1 < 2^64 := by decide
  unfold effectiveAlign
  split <;> rename_i h
  · have : align.toNat = 0 := by simp at h; rw [h]; rfl
    have h_one : (1 : UInt64).toNat = 1 := rfl
    rw [h_one]; omega
  · omega

-- ============================================================================
-- Bounds predicate. Pure — about UInt64 arithmetic.
-- ============================================================================

/-- An offset+length window fits inside `[0, size)`. Uses UInt64
    comparisons (saturating subtraction) to sidestep wrap. -/
def InRange (size offset length : UInt64) : Prop :=
  offset ≤ size ∧ length ≤ size - offset

instance (size offset length : UInt64) : Decidable (InRange size offset length) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- ============================================================================
-- Region — a `Segment` with a chosen mmap base.
-- All loader semantics (page math, BSS split, POSIX prot) live here.
-- ============================================================================

/-- A PT_LOAD segment with its chosen mmap base. After Layout, every
    absolute address Realize and Apply need is derivable from this
    struct alone. Pure data; IO that consumes Regions lives in
    `Exec`. -/
structure Region where
  base : UInt64
  seg  : Segment

namespace Region

-- ----------------------------------------------------------------------------
-- Page math (relative to the segment's vaddr).
-- ----------------------------------------------------------------------------

/-- Page-aligned segment-relative base. -/
def pageVaddr (r : Region) : UInt64 :=
  alignDown r.seg.vaddr (effectiveAlign r.seg.align)

/-- Page-aligned mmap length — the full reservation span. -/
def pageLength (r : Region) : UInt64 :=
  alignUp (r.seg.vaddr + r.seg.memsz) (effectiveAlign r.seg.align) - r.pageVaddr

/-- One past the last byte of the mmap'd range, segment-relative. -/
def pageEndAddr (r : Region) : UInt64 := r.pageVaddr + r.pageLength

/-- Offset within the mapped region for copied bytes (vaddr − pageVaddr). -/
def pageInset (r : Region) : UInt64 := r.seg.vaddr - r.pageVaddr

/-- Page-aligned length of the file-backed overlay. -/
def fileOverlayLen (r : Region) : UInt64 :=
  alignUp (r.pageInset + r.seg.filesz) (effectiveAlign r.seg.align)

/-- Page-aligned file offset for the overlay's `mmap(2)`. -/
def fileOffset (r : Region) : UInt64 :=
  alignDown r.seg.offset (effectiveAlign r.seg.align)

-- ----------------------------------------------------------------------------
-- Absolute addresses (post-base) — what Realize and Apply consume.
-- ----------------------------------------------------------------------------

/-- Absolute mmap base address (page-aligned). -/
def absVaddr (r : Region) : UInt64 := r.base + r.pageVaddr

/-- Length of the entire region — same as `pageLength`. -/
abbrev length (r : Region) : UInt64 := r.pageLength

/-- POSIX `PROT_*` bits derived from gabi `PF_*`. -/
def prot (r : Region) : UInt32 :=
  (if r.seg.perm.read  then (1 : UInt32) else 0) |||
  (if r.seg.perm.write then (2 : UInt32) else 0) |||
  (if r.seg.perm.exec  then (4 : UInt32) else 0)

-- ----------------------------------------------------------------------------
-- BSS split — two regimes:
--
--   • Partial-page BSS: bytes from `filesz` to the end of the
--     overlay's last partial page. These pages are file-backed
--     (mmap'd from the file), and the bytes past EOF are *not*
--     guaranteed to be zero — the linker might leave non-zero data
--     there. We zero them explicitly via `partialBssAddr/Len`.
--
--   • Anon BSS: bytes past the file overlay, i.e. full pages of BSS
--     that have no file backing. These are anonymous mappings; the
--     kernel zero-fills `MAP_ANONYMOUS` pages, so `mmapReserve` over
--     this span is sufficient — no explicit zero needed.
-- ----------------------------------------------------------------------------

/-- True when the segment has any file-backed bytes. -/
def hasFileBacked (r : Region) : Bool := r.fileOverlayLen > 0

/-- Absolute start of the partial-page BSS zero-fill window. Inside
    the file overlay, between `filesz` and the overlay's page-aligned
    end. -/
def partialBssAddr (r : Region) : UInt64 :=
  r.absVaddr + r.pageInset + r.seg.filesz

/-- Length of the partial-page BSS. -/
def partialBssLen (r : Region) : UInt64 :=
  r.fileOverlayLen - (r.pageInset + r.seg.filesz)

/-- True iff there are partial-page BSS bytes to zero. -/
def hasPartialBss (r : Region) : Bool := r.partialBssLen > 0

/-- Absolute start of the full-page BSS region (past the overlay). -/
def anonBssAddr (r : Region) : UInt64 := r.absVaddr + r.fileOverlayLen

/-- Length of the full-page BSS region. -/
def anonBssLen (r : Region) : UInt64 := r.length - r.fileOverlayLen

/-- True iff the segment has full-page BSS past the file overlay. -/
def hasAnonBss (r : Region) : Bool := r.anonBssLen > 0

-- ----------------------------------------------------------------------------
-- Structural-soundness theorems for the page math.
-- ----------------------------------------------------------------------------

/-- Page-aligned vaddr is ≤ raw vaddr. -/
theorem pageVaddr_le_vaddr (r : Region) : r.pageVaddr ≤ r.seg.vaddr :=
  alignDown_le _ _

/-- The BSS / patch write window fits inside the page-aligned mmap
    region. Discharged from `Segment.addrBound`. -/
theorem insetMemszLePageLength (r : Region) :
    r.pageInset.toNat + r.seg.memsz.toNat ≤ r.pageLength.toNat := by
  let ea := effectiveAlign r.seg.align
  have h_ea_ne : ea ≠ 0 := effectiveAlign_ne_zero r.seg.align
  have h_pv_le_v : r.pageVaddr ≤ r.seg.vaddr := r.pageVaddr_le_vaddr
  have h_pv_le_v_nat : r.pageVaddr.toNat ≤ r.seg.vaddr.toNat :=
    UInt64.le_iff_toNat_le.mp h_pv_le_v
  have h_vmea : (r.seg.vaddr + r.seg.memsz).toNat + ea.toNat < 2^64 := by
    have h_vm_no_wrap : r.seg.vaddr.toNat + r.seg.memsz.toNat < 2^64 := by
      have := ea_no_wrap r.seg.vaddr r.seg.memsz r.seg.align r.seg.addrBound; omega
    have h_vm_eq : (r.seg.vaddr + r.seg.memsz).toNat
        = r.seg.vaddr.toNat + r.seg.memsz.toNat := by
      rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_vm_no_wrap
    rw [h_vm_eq]; exact ea_no_wrap _ _ _ r.seg.addrBound
  have h_au_ge : r.seg.vaddr + r.seg.memsz ≤ alignUp (r.seg.vaddr + r.seg.memsz) ea :=
    alignUp_ge _ _ h_ea_ne h_vmea
  have h_au_ge_nat :
      r.seg.vaddr.toNat + r.seg.memsz.toNat ≤
        (alignUp (r.seg.vaddr + r.seg.memsz) ea).toNat := by
    have h_vm_eq : (r.seg.vaddr + r.seg.memsz).toNat
        = r.seg.vaddr.toNat + r.seg.memsz.toNat := by
      have h_vm_no_wrap : r.seg.vaddr.toNat + r.seg.memsz.toNat < 2^64 := by
        have := ea_no_wrap r.seg.vaddr r.seg.memsz r.seg.align r.seg.addrBound; omega
      rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_vm_no_wrap
    have := UInt64.le_iff_toNat_le.mp h_au_ge; rw [h_vm_eq] at this; exact this
  have h_au_le_pv :
      r.pageVaddr ≤ alignUp (r.seg.vaddr + r.seg.memsz) ea := by
    apply UInt64.le_iff_toNat_le.mpr; omega
  have h_pl_nat : r.pageLength.toNat =
      (alignUp (r.seg.vaddr + r.seg.memsz) ea).toNat - r.pageVaddr.toNat := by
    show (alignUp _ _ - r.pageVaddr).toNat = _
    rw [UInt64.toNat_sub_of_le _ _ h_au_le_pv]
  have h_pi_nat : r.pageInset.toNat = r.seg.vaddr.toNat - r.pageVaddr.toNat := by
    show (r.seg.vaddr - r.pageVaddr).toNat = _
    rw [UInt64.toNat_sub_of_le _ _ h_pv_le_v]
  rw [h_pi_nat, h_pl_nat]; omega

/-- Two regions are disjoint when their `[pageVaddr, pageEndAddr)`
    ranges don't overlap. -/
def disjoint (r₁ r₂ : Region) : Prop :=
  r₁.pageEndAddr ≤ r₂.pageVaddr ∨ r₂.pageEndAddr ≤ r₁.pageVaddr

end Region

-- ============================================================================
-- ObjectLayout — per-object plan with chosen base.
-- ============================================================================

/-- Layout for a single loaded object. `base` is the absolute mmap
    address at which the object's segments will be placed. For
    `ET_EXEC` (vaddrs already absolute) `base = 0`. For `ET_DYN`,
    Layout picks `base = dynAnchor + cumulative_offset` so each
    object lives in its own non-overlapping slot starting at
    `dynAnchor`. -/
structure ObjectLayout where
  base   : UInt64
  /-- The `e_entry` field. `none` for objects we never enter. -/
  entry  : Option UInt64
  /-- True for the main executable. -/
  isMain : Bool

/-- Hardcoded anchor for the first `ET_DYN` object. Picked to avoid
    colliding with the host process's typical mappings on x86-64 /
    aarch64 (heap, libc, etc., usually in the low GB). -/
def dynAnchor : UInt64 := 0x80000000

/-- The contiguous span an array of segments needs (relative to the
    object's base). -/
def objectSpan (base : UInt64) (segments : Array Segment) : UInt64 :=
  segments.foldl (init := 0) fun acc s =>
    max acc (Region.mk base s).pageEndAddr

/-- Layout for a single elaborated ELF. -/
def objectLayout (isMain : Bool) (base : UInt64) (elf : Elf) : ObjectLayout :=
  let entry := if isMain then some elf.entry else none
  { base, entry, isMain }

/-- Segments are pairwise disjoint. -/
def segmentsPairwiseDisjoint (base : UInt64) (segs : Array Segment) : Prop :=
  ∀ i j (_ : i < segs.size) (_ : j < segs.size),
    i ≠ j → Region.disjoint (Region.mk base segs[i]) (Region.mk base segs[j])

/-- Segments are sorted by page-aligned vaddr with each one's end ≤
    the next one's start. -/
def segmentsSorted (base : UInt64) (segs : Array Segment) : Prop :=
  ∀ i, ∀ _ : i < segs.size, ∀ j, ∀ _ : j < segs.size,
    i < j → (Region.mk base segs[i]).pageEndAddr ≤
            (Region.mk base segs[j]).pageVaddr

instance (base : UInt64) (segs : Array Segment) :
    Decidable (segmentsSorted base segs) := by
  unfold segmentsSorted; infer_instance

-- ============================================================================
-- Layout-stage entry points.
-- ============================================================================

/-- Assign an mmap base to each elf in BFS order. `.exec` objects
    keep `0`; `.dyn` (and others) start at `dynAnchor` and stack by
    `alignUp objectSpan 0x1000`. -/
def assignBases (elfs : Array Elf) : Array UInt64 :=
  let f : (Array UInt64 × UInt64) → Elf → (Array UInt64 × UInt64) :=
    fun (bases, cursor) elf =>
      if elf.elfType == .exec then
        (bases.push 0, cursor)
      else
        let advance := alignUp (objectSpan 0 elf.segments) 0x1000
        (bases.push cursor, cursor + advance)
  (elfs.foldl (init := (Array.mkEmpty elfs.size, dynAnchor)) f).fst

theorem assignBases_size (elfs : Array Elf) : (assignBases elfs).size = elfs.size := by
  unfold assignBases
  let motive : Nat → Array UInt64 × UInt64 → Prop := fun n p => p.fst.size = n
  show motive elfs.size _
  refine Array.foldl_induction motive ?_ ?_
  · show (Array.mkEmpty elfs.size).size = 0; simp
  · intro idx ⟨bases, cursor⟩ ih
    have ih' : bases.size = idx.val := ih
    show (if (elfs[idx.val].elfType == Elaborate.ElfType.exec) = true
            then (bases.push 0, cursor)
            else (bases.push cursor, cursor + _)).fst.size = idx.val + 1
    by_cases hExec : (elfs[idx.val].elfType == Elaborate.ElfType.exec) = true
    · rw [if_pos hExec]; simp [ih']
    · rw [if_neg hExec]; simp [ih']

/-- Build the per-elf layouts. The `segmentsSorted` witness is on the
    *base-zero* segments view; that's a vaddr-only check (page math
    is invariant under base translation). -/
def layouts (elfs : Array Elf) :
    Except String { a : Array ObjectLayout //
      a.size = elfs.size ∧
      ∀ (i : Nat) (h : i < elfs.size), segmentsSorted 0 elfs[i].segments } :=
  let bases := assignBases elfs
  have hBases : bases.size = elfs.size := assignBases_size elfs
  let arr := elfs.mapFinIdx fun i elf h =>
    objectLayout (i == 0) (bases[i]'(hBases ▸ h)) elf
  match harr : elfs.findIdx? (fun elf => ¬ segmentsSorted 0 elf.segments) with
  | some i =>
    .error s!"layouts: object[{i}] has malformed PT_LOAD segments"
  | none =>
    .ok ⟨arr, by
      refine ⟨by simp [arr], ?_⟩
      intro i hi
      have hall : ∀ x ∈ elfs, decide (¬ segmentsSorted 0 x.segments) = false :=
        Array.findIdx?_eq_none_iff.mp harr
      have hi_in : elfs[i] ∈ elfs := Array.getElem_mem hi
      have := hall elfs[i] hi_in
      simp at this
      exact this⟩

-- ============================================================================
-- Bounds proofs consumed by Apply.
-- ============================================================================

/-- The BSS write window fits inside the segment's page-aligned mmap
    range. -/
theorem bss_inRange (r : Region) :
    InRange r.pageLength
      (r.pageInset + r.seg.filesz) (r.seg.memsz - r.seg.filesz) := by
  have h_fm := r.seg.fileszLeMemsz
  have h_inset := r.insetMemszLePageLength
  have h_fm_nat : r.seg.filesz.toNat ≤ r.seg.memsz.toNat := UInt64.le_iff_toNat_le.mp h_fm
  have h_pif_no_wrap : r.pageInset.toNat + r.seg.filesz.toNat < 2^64 := by
    have h_2_64 : r.pageLength.toNat < 2^64 := r.pageLength.toNat_lt
    omega
  have h_pif_nat : (r.pageInset + r.seg.filesz).toNat
      = r.pageInset.toNat + r.seg.filesz.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_pif_no_wrap
  have h_mf_nat : (r.seg.memsz - r.seg.filesz).toNat
      = r.seg.memsz.toNat - r.seg.filesz.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ h_fm]
  refine ⟨?_, ?_⟩
  · rw [UInt64.le_iff_toNat_le, h_pif_nat]; omega
  · have h_le1 : r.pageInset + r.seg.filesz ≤ r.pageLength := by
      rw [UInt64.le_iff_toNat_le, h_pif_nat]; omega
    rw [UInt64.le_iff_toNat_le, h_mf_nat,
        UInt64.toNat_sub_of_le _ _ h_le1, h_pif_nat]
    omega

/-- A rela's 8-byte write window fits inside the segment's mmap
    range. -/
theorem patch_inRange (r : Region) (r_offset : UInt64)
    (h_cov : Elaborate.coversRela r.seg.vaddr r.seg.memsz r_offset) :
    InRange r.pageLength (r_offset - r.pageVaddr) 8 := by
  obtain ⟨h_lo, h_hi⟩ := h_cov
  have h_inset := r.insetMemszLePageLength
  have h_pv_le_v : r.pageVaddr ≤ r.seg.vaddr := r.pageVaddr_le_vaddr
  have h_pv_le_v_nat : r.pageVaddr.toNat ≤ r.seg.vaddr.toNat :=
    UInt64.le_iff_toNat_le.mp h_pv_le_v
  have h_pi_nat : r.pageInset.toNat = r.seg.vaddr.toNat - r.pageVaddr.toNat := by
    show (r.seg.vaddr - r.pageVaddr).toNat = _
    rw [UInt64.toNat_sub_of_le _ _ h_pv_le_v]
  have h_pv_le_ro : r.pageVaddr ≤ r_offset := by
    apply UInt64.le_iff_toNat_le.mpr; omega
  have h_off_nat : (r_offset - r.pageVaddr).toNat
      = r_offset.toNat - r.pageVaddr.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ h_pv_le_ro]
  refine ⟨?_, ?_⟩
  · rw [UInt64.le_iff_toNat_le, h_off_nat]; omega
  · have h_le1 : r_offset - r.pageVaddr ≤ r.pageLength := by
      rw [UInt64.le_iff_toNat_le, h_off_nat]; omega
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ h_le1, h_off_nat]
    show (8 : UInt64).toNat ≤ _
    have h_eight : (8 : UInt64).toNat = 8 := rfl
    rw [h_eight]; omega

theorem inRange_4_of_8 {size offset : UInt64}
    (h : InRange size offset 8) : InRange size offset 4 := by
  refine ⟨h.1, ?_⟩
  have h_eight : (8 : UInt64).toNat = 8 := rfl
  have h_four  : (4 : UInt64).toNat = 4 := rfl
  have := UInt64.le_iff_toNat_le.mp h.2
  rw [h_eight] at this
  apply UInt64.le_iff_toNat_le.mpr
  rw [h_four]; omega

end LeanLoad.Layout

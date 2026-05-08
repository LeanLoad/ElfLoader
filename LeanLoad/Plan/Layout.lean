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
    end. These bytes are file-mapped (whatever's at that file offset),
    not zero, so we explicitly zero them. -/
def partialBssAddr (r : Region) : UInt64 :=
  r.absVaddr + r.pageInset + r.seg.filesz

/-- Length of the partial-page BSS. -/
def partialBssLen (r : Region) : UInt64 :=
  r.fileOverlayLen - (r.pageInset + r.seg.filesz)

/-- True iff there are partial-page BSS bytes to zero. -/
def hasPartialBss (r : Region) : Bool := r.partialBssLen > 0

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

-- ----------------------------------------------------------------------------
-- No-wrap precondition for the static safety proofs. Every UInt64 sum
-- the per-region safety predicates need is bounded by `absVaddr +
-- length`, so requiring that one sum to fit in 2^64 lets the proofs
-- treat all the sub-sums as Nat addition.
-- ----------------------------------------------------------------------------

/-- The region's absolute mmap range fits in `UInt64`. -/
def NoWrap (r : Region) : Prop :=
  r.absVaddr.toNat + r.length.toNat ≤ 2 ^ 64

instance (r : Region) : Decidable r.NoWrap := by
  unfold NoWrap; infer_instance

end Region

-- ============================================================================
-- Per-object plan: a chosen mmap base. ET_DYN-only (ET_EXEC is
-- rejected at elaborate time). Production gets `base` from
-- `Runtime.mmapAnonAlloc` (kernel-picked); tests pass `dynAnchor`
-- as a synthetic value.
-- ============================================================================

/-- Test-only synthetic base. Production uses the kernel-picked
    address from `Runtime.mmapAnonAlloc`; this constant exists so
    pure-stage `#guard`s in `Example.lean` can drive the planner
    without IO. -/
def dynAnchor : UInt64 := 0x80000000

/-- The contiguous span an array of segments needs (relative to the
    object's base). -/
def objectSpan (base : UInt64) (segments : Array Segment) : UInt64 :=
  segments.foldl (init := 0) fun acc s =>
    max acc (Region.mk base s).pageEndAddr

/-- Cumulative reservation span across every loaded object —
    `Σ alignUp objectSpan 0x1000`. This is the `len` to pass to
    `Runtime.mmapAnonAlloc` at the IO boundary. -/
def totalSpan (elfs : Array Elf) : UInt64 :=
  elfs.foldl (init := 0) fun acc elf =>
    acc + alignUp (objectSpan 0 elf.segments) 0x1000

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
-- Layout-stage entry points (pure — `base` is parameterized so tests
-- can pass any UInt64 and production can pass the kernel-picked one).
-- ============================================================================

/-- Assign per-elf mmap bases starting from `base`, stacking each by
    `alignUp objectSpan 0x1000`. Pure: `base` is the input, not
    hardcoded. -/
def assignBases (base : UInt64) (elfs : Array Elf) : Array UInt64 :=
  let f : (Array UInt64 × UInt64) → Elf → (Array UInt64 × UInt64) :=
    fun (bases, cursor) elf =>
      let advance := alignUp (objectSpan 0 elf.segments) 0x1000
      (bases.push cursor, cursor + advance)
  (elfs.foldl (init := (Array.mkEmpty elfs.size, base)) f).fst

theorem assignBases_size (base : UInt64) (elfs : Array Elf) :
    (assignBases base elfs).size = elfs.size := by
  unfold assignBases
  let motive : Nat → Array UInt64 × UInt64 → Prop := fun n p => p.fst.size = n
  show motive elfs.size _
  refine Array.foldl_induction motive ?_ ?_
  · show (Array.mkEmpty elfs.size).size = 0; simp
  · intro idx ⟨bases, cursor⟩ ih
    have ih' : bases.size = idx.val := ih
    show (bases.push cursor, cursor + _).fst.size = idx.val + 1
    simp [ih']

/-- Build the per-elf bases and validate `segmentsSorted` per elf.
    `base` is the reservation start; production threads it from
    `Runtime.mmapAnonAlloc`. The witness is on the *base-zero*
    segments view (page math is base-translation invariant). -/
def layouts (base : UInt64) (elfs : Array Elf) :
    Except String { bases : Array UInt64 //
      bases.size = elfs.size ∧
      ∀ (i : Nat) (h : i < elfs.size), segmentsSorted 0 elfs[i].segments } :=
  let bases := assignBases base elfs
  have hBases : bases.size = elfs.size := assignBases_size base elfs
  match harr : elfs.findIdx? (fun elf => ¬ segmentsSorted 0 elf.segments) with
  | some i =>
    .error s!"layouts: object[{i}] has malformed PT_LOAD segments"
  | none =>
    .ok ⟨bases, hBases, by
      intro i hi
      have hall : ∀ x ∈ elfs, decide (¬ segmentsSorted 0 x.segments) = false :=
        Array.findIdx?_eq_none_iff.mp harr
      have hi_in : elfs[i] ∈ elfs := Array.getElem_mem hi
      have := hall elfs[i] hi_in
      simp at this
      exact this⟩

end LeanLoad.Layout

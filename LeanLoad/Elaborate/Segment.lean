/-
The post-layout segment view: a `RawSegment` (gabi-07 spec) extended
with pre-computed loader views (page-aligned mmap addresses + sizes,
POSIX `PROT_*` bits) and the page-arithmetic invariants downstream
needs. The page math is discharged once at `Segment.ofPhdr`;
`Exec.realizeSegment` and `applyPatch` read the stored fields.

For the spec-only view (no loader concerns), see `RawSegment` in
`Elaborate/RawSegment.lean`.
-/

import LeanLoad.Elaborate.RawSegment

namespace LeanLoad.Elaborate

open LeanLoad.Parse (RawPhdr RawRela)

-- ============================================================================
-- Page-arithmetic helpers (loader-level mmap concerns).
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
-- The post-layout segment.
-- ============================================================================

/-- The post-layout segment: a `RawSegment` plus pre-computed loader
    views (page-aligned mmap addresses + sizes, POSIX `PROT_*`) and
    the arithmetic invariants downstream consumes. The page math is
    discharged once at `Segment.ofPhdr`; `Exec.realizeSegment` and
    `applyPatch` read the stored fields and skip runtime checks. -/
structure Segment extends RawSegment where
  /-- Page-aligned mmap base. -/
  pageVaddr       : UInt64
  /-- mmap length (page-aligned span). -/
  pageLength      : UInt64
  /-- One past last byte of mmap'd range. -/
  pageEndAddr     : UInt64
  /-- Offset within mapped region for copied bytes. -/
  pageInset       : UInt64
  /-- Page-aligned length of file-backed mmap range. -/
  fileLenPaged    : UInt64
  /-- Page-aligned file offset for `mmap(2)`. -/
  fileOffsetPaged : UInt64
  /-- POSIX `PROT_*` bits. -/
  prot            : UInt32
  -- Coherence with computed forms (definitionally `rfl` from `ofPhdr`).
  pageVaddr_eq       : pageVaddr       = alignDown vaddr (if align == 0 then 1 else align)
  pageLength_eq      : pageLength      =
    alignUp (vaddr + memsz) (if align == 0 then 1 else align) - pageVaddr
  pageEndAddr_eq     : pageEndAddr     = pageVaddr + pageLength
  pageInset_eq       : pageInset       = vaddr - pageVaddr
  fileLenPaged_eq    : fileLenPaged    =
    alignUp (pageInset + filesz) (if align == 0 then 1 else align)
  fileOffsetPaged_eq : fileOffsetPaged = alignDown offset (if align == 0 then 1 else align)
  -- Pre-discharged arithmetic invariants.
  /-- Page-aligned vaddr is ≤ raw vaddr. -/
  pageVaddr_le_vaddr : pageVaddr ≤ vaddr
  /-- The BSS / patch write window fits inside the page-aligned
      mmap region. -/
  insetMemszLePageLength : pageInset.toNat + memsz.toNat ≤ pageLength.toNat

/-- Lift a decidable proposition into `Except` (with `PLift` to bridge
    `Prop` through `Except`'s `Type` parameter). -/
private def assertProp (p : Prop) [Decidable p] (msg : String) :
    Except String (PLift p) :=
  if h : p then .ok ⟨h⟩ else .error msg

private def effectiveAlign (align : UInt64) : UInt64 :=
  if align == 0 then 1 else align

private theorem effectiveAlign_ne_zero (align : UInt64) :
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

/-- Smart constructor: build a `Segment` from a `RawPhdr` (assumed
    PT_LOAD by the caller — `Elaborate.elaborate` filters its input
    array by `p_type`) and pre-located rela arrays, decidably checking
    gabi-07 per-segment invariants and discharging the loader-stage
    page-arithmetic facts. -/
def Segment.ofPhdr (phdr : RawPhdr)
    (rela jmprel : Array { r : RawRela // coversRela phdr.p_vaddr phdr.p_memsz r }) :
    Except String Segment := do
  let ⟨fileszLeMemsz⟩ ← assertProp (phdr.p_filesz ≤ phdr.p_memsz)
    s!"p_filesz=0x{phdr.p_filesz.toNat} > p_memsz=0x{phdr.p_memsz.toNat} \
       (gabi-07 § Program Header)"
  let ⟨alignPow2⟩ ← assertProp
    (phdr.p_align = 0 ∨ (phdr.p_align &&& (phdr.p_align - 1)) = 0)
    s!"p_align=0x{phdr.p_align.toNat} is not a power of 2 \
       (gabi-07 § Program Header)"
  let ⟨alignCong⟩ ← assertProp
    (phdr.p_align = 0 ∨ phdr.p_vaddr % phdr.p_align = phdr.p_offset % phdr.p_align)
    "alignment congruence violated (gabi-07: p_vaddr ≡ p_offset mod p_align)"
  let ⟨addrBound⟩ ← assertProp
    (phdr.p_vaddr.toNat + phdr.p_memsz.toNat + phdr.p_align.toNat < 2 ^ 48)
    s!"p_vaddr+p_memsz+p_align \
       (0x{phdr.p_vaddr.toNat}+0x{phdr.p_memsz.toNat}+0x{phdr.p_align.toNat}) \
       exceeds 48-bit bound"
  let ea          := effectiveAlign phdr.p_align
  let pageVaddr   := alignDown phdr.p_vaddr ea
  let pageLength  := alignUp (phdr.p_vaddr + phdr.p_memsz) ea - pageVaddr
  let pageInset   := phdr.p_vaddr - pageVaddr
  let pageEndAddr := pageVaddr + pageLength
  -- Discharge the two arithmetic invariants once.
  have h_ea_ne : ea ≠ 0 := effectiveAlign_ne_zero phdr.p_align
  have h_pv_le_v : pageVaddr ≤ phdr.p_vaddr := alignDown_le _ _
  have h_pv_le_v_nat : pageVaddr.toNat ≤ phdr.p_vaddr.toNat :=
    UInt64.le_iff_toNat_le.mp h_pv_le_v
  have h_vmea : (phdr.p_vaddr + phdr.p_memsz).toNat + ea.toNat < 2^64 := by
    have h_vm_no_wrap : phdr.p_vaddr.toNat + phdr.p_memsz.toNat < 2^64 := by
      have := ea_no_wrap phdr.p_vaddr phdr.p_memsz phdr.p_align addrBound; omega
    have h_vm_eq : (phdr.p_vaddr + phdr.p_memsz).toNat
        = phdr.p_vaddr.toNat + phdr.p_memsz.toNat := by
      rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_vm_no_wrap
    rw [h_vm_eq]; exact ea_no_wrap _ _ _ addrBound
  have h_au_ge : phdr.p_vaddr + phdr.p_memsz ≤ alignUp (phdr.p_vaddr + phdr.p_memsz) ea :=
    alignUp_ge _ _ h_ea_ne h_vmea
  have h_au_ge_nat :
      phdr.p_vaddr.toNat + phdr.p_memsz.toNat ≤
        (alignUp (phdr.p_vaddr + phdr.p_memsz) ea).toNat := by
    have h_vm_eq : (phdr.p_vaddr + phdr.p_memsz).toNat
        = phdr.p_vaddr.toNat + phdr.p_memsz.toNat := by
      have h_vm_no_wrap : phdr.p_vaddr.toNat + phdr.p_memsz.toNat < 2^64 := by
        have := ea_no_wrap phdr.p_vaddr phdr.p_memsz phdr.p_align addrBound; omega
      rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_vm_no_wrap
    have := UInt64.le_iff_toNat_le.mp h_au_ge; rw [h_vm_eq] at this; exact this
  have h_au_le_pv :
      pageVaddr ≤ alignUp (phdr.p_vaddr + phdr.p_memsz) ea := by
    apply UInt64.le_iff_toNat_le.mpr; omega
  have h_pl_nat : pageLength.toNat =
      (alignUp (phdr.p_vaddr + phdr.p_memsz) ea).toNat - pageVaddr.toNat := by
    show (alignUp _ _ - pageVaddr).toNat = _
    rw [UInt64.toNat_sub_of_le _ _ h_au_le_pv]
  have h_pi_nat : pageInset.toNat = phdr.p_vaddr.toNat - pageVaddr.toNat := by
    show (phdr.p_vaddr - pageVaddr).toNat = _
    rw [UInt64.toNat_sub_of_le _ _ h_pv_le_v]
  have h_inset_memsz_le_pl :
      pageInset.toNat + phdr.p_memsz.toNat ≤ pageLength.toNat := by
    rw [h_pi_nat, h_pl_nat]; omega
  return {
    vaddr := phdr.p_vaddr, memsz := phdr.p_memsz,
    filesz := phdr.p_filesz, offset := phdr.p_offset,
    perm := Prot.ofFlags phdr.p_flags, align := phdr.p_align,
    fileszLeMemsz, alignPow2, alignCong, addrBound,
    pageVaddr, pageLength, pageEndAddr, pageInset,
    fileLenPaged    := alignUp (pageInset + phdr.p_filesz) ea,
    fileOffsetPaged := alignDown phdr.p_offset ea,
    prot := (if (phdr.p_flags &&& PF_R) != 0 then (1 : UInt32) else 0) |||
            (if (phdr.p_flags &&& PF_W) != 0 then (2 : UInt32) else 0) |||
            (if (phdr.p_flags &&& PF_X) != 0 then (4 : UInt32) else 0),
    pageVaddr_eq := rfl, pageLength_eq := rfl, pageEndAddr_eq := rfl,
    pageInset_eq := rfl, fileLenPaged_eq := rfl, fileOffsetPaged_eq := rfl,
    pageVaddr_le_vaddr := h_pv_le_v,
    insetMemszLePageLength := h_inset_memsz_le_pl,
    rela, jmprel
  }

/-- Two segments are disjoint when their `[pageVaddr, pageEndAddr)`
    ranges don't overlap. -/
def Segment.disjoint (s₁ s₂ : Segment) : Prop :=
  s₁.pageEndAddr ≤ s₂.pageVaddr ∨ s₂.pageEndAddr ≤ s₁.pageVaddr

end LeanLoad.Elaborate

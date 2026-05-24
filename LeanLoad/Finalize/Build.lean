/-
Builder: turn a `BoundPlan` into a complete pure `Finalize.Result` ready for the
runtime interpreter. Fully constructive — no decidable safety fallback, no
`.error` branch for safety.

Public entry point:
  • `build`     — pure: `BoundPlan → Finalize.Result bp`.
                  Returns intrinsic-safe `LoadOps` plus entry/init/fini
                  `CallOp`s over the same bound plan.
                  The safety fields are built structurally:
                    1. `buildSegment` per segment — combines
                       `setupSegment_*_eq` (closed form of (addr, len))
                       with `BoundPlan.segment_*_in_rsv` (per-op
                       `Range.InRange`) and `bakeReloc` characterisation +
                       `bakeSegmentRelocs_storesInvariant`.
                    2. `buildElf` per elf — assembles
                       `buildElfSegments`'s output + within-elf
                       disjointness from
                       `BoundPlan.within_elf_mmapRange_disjoint`.
                    3. `buildLoadElves` across elves — threads
                       `ElfBuildInvariant` so the cross-elf
                       disjointness in `build` can chain to
                       `BoundPlan.cross_elf_mmapRange_disjoint`.
                  The only `Except` failure path is `bakeReloc`'s
                  32-bit overflow check (psABI per-relocation
                  `OVERFLOW_CHECK`).
Private helpers resolve entry/init/fini targets through the per-elf base; ET_DYN
entries get the chosen base added, zero entries are skipped for init/fini arrays,
and every emitted address carries an executable-segment witness.

`Main.realize` consumes `build`'s packed result via the runtime interpreter. There
is no separate `safe` entry point.
-/

import LeanLoad.Finalize.LoadOps
import LeanLoad.Finalize.Reloc
import LeanLoad.Finalize.BoundPlan

namespace LeanLoad.Finalize

open LeanLoad
open LeanLoad.Parse (Elf)
open LeanLoad.Reloc.ABI (Formula)

-- ============================================================================
-- buildSegment — assemble one intrinsic-safe `SegmentOps`.
-- The safety fields are built
-- by chaining `setupSegment_*_eq` (closed forms of the ops) with the
-- matching `BoundPlan.segment_*_in_rsv` theorems. Stores come from
-- `bakeSegmentRelocs`; their bound is `bakeSegmentRelocs_storesInvariant`
-- with the universal predicate "byteLen ≤ 8 ∧ addr = base +
-- entry.r_offset for some entry whose `covered` witness gives
-- `segment_storeRange_in_rsv`".
-- ============================================================================

/-- Build one intrinsic-safe `SegmentOps` + the `mmap_eq` equality that ties
    the built mmap back to its
    `setupSegment` source (needed by the enclosing `buildElfSegments`
    to chain to `within_elf_mmapRange_disjoint`). The only `Except`
    failure source is `bakeSegmentRelocs`'s 32-bit overflow check —
    safety itself is established structurally. -/
def buildSegment (bp : BoundPlan) (i : Fin bp.objCount)
    (j : Fin (bp.elfAt i).segmentCount) :
    Except String { so : SegmentOps bp.rsv.addr bp.rsv.len bp.objCount //
      so.mmap =
        (setupSegment (bp.segAt i j) (bp.handleAt i) (bp.baseAt i)).mmap } := do
  let elfs := bp.objectElfs
  let objCount := bp.objCount
  have h_elfs : elfs.size = objCount := bp.objectElfs_size
  let basesArr := bp.bases.toArray
  have h_bases : basesArr.size = objCount := bp.bases.size_toArray
  let sp := bp.segAt i j
  let handle := bp.handleAt i
  let base := bp.baseAt i
  -- Don't destructure `setupSegment` — keep the projection form so the
  -- characterisation lemmas (`setupSegment_*_eq`) align on the goal.
  let setup := setupSegment sp handle base
  -- Use the sized variant so `sp.relocs : Array (Entry objCount sp.segment)`
  -- is accepted directly — no `▸` cast on the relocs array.
  match h_bake : bakeSegmentRelocs bp.formula elfs h_elfs basesArr
                   h_bases base sp.segment sp.relocs with
  | .error e => .error e
  | .ok stores =>
    -- `SegmentOps extends SegmentSetup`, so this inherits mmap/zero/mprotect
    -- from `setup`, adds the layout/stores, and proves each emitted range stays
    -- inside the reservation.
    let so : SegmentOps bp.rsv.addr bp.rsv.len objCount :=
      { setup with
        layout := sp
        stores := stores
        mmapInRange := by
          intro m h_m
          have ⟨h_addr, h_len⟩ := setupSegment_mmap_eq sp handle base m h_m
          rw [h_addr, h_len]
          exact bp.segment_mmapRange_in_rsv i j
        zeroInRange := by
          intro z h_z
          have ⟨h_addr, h_len⟩ := setupSegment_zero_eq sp handle base z h_z
          rw [h_addr, h_len]
          exact bp.segment_zeroRange_in_rsv i j
        storesInRange := by
          intro s h_s
          refine bakeSegmentRelocs_storesInvariant bp.formula elfs h_elfs
            basesArr h_bases base sp.segment sp.relocs
            (fun s' => Range.InRange s'.addr s'.byteLen bp.rsv.addr bp.rsv.len)
            ?_ stores h_bake s h_s
          intro e s' h_br
          obtain ⟨h_addr, _h_size⟩ := bakeReloc_ok_some bp.formula elfs
            h_elfs basesArr h_bases base sp.segment e s' h_br
          have h_byteLen := bakeReloc_byteLen_le_8 bp.formula elfs
            h_elfs basesArr h_bases base sp.segment e s' h_br
          rw [h_addr]
          exact bp.segment_storeRange_in_rsv i j e.r_offset e.covered
            s'.byteLen h_byteLen
        mprotectInRange := by
          have ⟨h_addr, h_len⟩ := setupSegment_mprotect_eq sp handle base
          rw [h_addr, h_len]
          exact bp.segment_mprotectRange_in_rsv i j }
    -- The `mmap_eq` field — `so.mmap = setup.mmap` by construction (rfl).
    .ok ⟨so, rfl⟩

-- ============================================================================
-- buildElfSegments — build an elf's intrinsic-safe segment array with
-- per-index `mmap_eq` invariants.
-- ============================================================================

/-- Build an elf's segments array with per-index `mmap_eq` invariants.
    The `mmap_eq` invariant lets
    `buildElf` chain to `within_elf_mmapRange_disjoint`. -/
def buildElfSegments (bp : BoundPlan) (i : Fin bp.objCount) :
    Except String { result : Array (SegmentOps bp.rsv.addr bp.rsv.len bp.objCount) //
      result.size = (bp.elfAt i).segmentCount ∧
      (∀ k (h_k : k < result.size)
        (h_src : k < (bp.elfAt i).segmentCount),
        (result[k]'h_k).mmap =
          (setupSegment (bp.segAt i ⟨k, h_src⟩) (bp.handleAt i) (bp.baseAt i)).mmap) } := do
  let built ← buildFinFunction (n := (bp.elfAt i).segmentCount)
    (β := fun j =>
      { so : SegmentOps bp.rsv.addr bp.rsv.len bp.objCount //
        so.mmap =
          (setupSegment (bp.segAt i j) (bp.handleAt i) (bp.baseAt i)).mmap })
    (fun j => buildSegment bp i j)
  let arr : Array (SegmentOps bp.rsv.addr bp.rsv.len bp.objCount) :=
    Array.ofFn fun j => (built j).val
  return ⟨arr, by simp [arr],
    by
      intro k h_k h_src
      let j : Fin (bp.elfAt i).segmentCount := ⟨k, h_src⟩
      have h_get : arr[k]'h_k = (built j).val := by
        simp [arr, j]
      rw [h_get]
      exact (built j).property⟩

-- ============================================================================
-- buildElf — assemble one intrinsic-safe `ElfOps`.
-- Within-elf disjointness chains `mmap_eq` (segment k's built mmap
-- matches setupSegment's output) with `setupSegment_mmap_eq` (closed form
-- of (addr, len)) into `within_elf_mmapRange_disjoint`'s conclusion.
-- ============================================================================

/-- Per-elf invariant carried across `buildLoadElves`: each elf's
    `segments` array has the matching length, and each built segment's
    `mmap` matches what `setupSegment` produced on the source segment.
    The cross-elf disjointness proof in `buildSafe` rewrites along
    these to land in `cross_elf_mmapRange_disjoint`. -/
private def ElfBuildInvariant (bp : BoundPlan) (i : Fin bp.objCount)
    (eo : ElfOps bp.rsv.addr bp.rsv.len bp.objCount) : Prop :=
  eo.segments.size = (bp.elfAt i).segmentCount ∧
  (∀ k (h_k : k < eo.segments.size)
    (h_src : k < (bp.elfAt i).segmentCount),
    (eo.segments[k]'h_k).mmap =
      (setupSegment (bp.segAt i ⟨k, h_src⟩) (bp.handleAt i) (bp.baseAt i)).mmap)

/-- Build one intrinsic-safe `ElfOps` + `ElfBuildInvariant`. -/
def buildElf (bp : BoundPlan) (i : Fin bp.objCount) :
    Except String { eo : ElfOps bp.rsv.addr bp.rsv.len bp.objCount //
      ElfBuildInvariant bp i eo } := do
  let ⟨segments, h_size, h_mmap⟩ ← buildElfSegments bp i
  let eo : ElfOps bp.rsv.addr bp.rsv.len bp.objCount :=
    { segments := segments
      mmapsDisjoint := by
        -- Within-elf mmap disjointness: for j₁ < j₂, both segments' mmaps
        -- come from setupSegment on the corresponding source segments.
        intro j₁ j₂ h_j₁ h_j₂ h_lt m₁ m₂ h_m₁ h_m₂
        have h_j₁_src : j₁ < (bp.elfAt i).segmentCount := by
          rw [h_size] at h_j₁; exact h_j₁
        have h_j₂_src : j₂ < (bp.elfAt i).segmentCount := by
          rw [h_size] at h_j₂; exact h_j₂
        have h_mmap_eq₁ := h_mmap j₁ h_j₁ h_j₁_src
        have h_mmap_eq₂ := h_mmap j₂ h_j₂ h_j₂_src
        have h_su₁ : (setupSegment (bp.segAt i ⟨j₁, h_j₁_src⟩) (bp.handleAt i)
              (bp.baseAt i)).mmap = some m₁ := by
          rw [← h_mmap_eq₁]; exact h_m₁
        have h_su₂ : (setupSegment (bp.segAt i ⟨j₂, h_j₂_src⟩) (bp.handleAt i)
              (bp.baseAt i)).mmap = some m₂ := by
          rw [← h_mmap_eq₂]; exact h_m₂
        have ⟨h_a₁, h_l₁⟩ := setupSegment_mmap_eq (bp.segAt i ⟨j₁, h_j₁_src⟩)
          (bp.handleAt i) (bp.baseAt i) m₁ h_su₁
        have ⟨h_a₂, h_l₂⟩ := setupSegment_mmap_eq (bp.segAt i ⟨j₂, h_j₂_src⟩)
          (bp.handleAt i) (bp.baseAt i) m₂ h_su₂
        have h_disj := bp.within_elf_mmapRange_disjoint i
          ⟨j₁, h_j₁_src⟩ ⟨j₂, h_j₂_src⟩ h_lt
        rw [h_a₁, h_l₁, h_a₂, h_l₂]; exact h_disj }
  let h_inv : ElfBuildInvariant bp i eo := ⟨h_size, h_mmap⟩
  return ⟨eo, h_inv⟩

-- ============================================================================
-- buildLoadElves — build the intrinsic-safe array of ElfOps with per-elf
-- `ElfBuildInvariant` invariants.
-- ============================================================================

/-- Build all elves with `ElfBuildInvariant` witnesses. -/
def buildLoadElves (bp : BoundPlan) :
    Except String { result : Array (ElfOps bp.rsv.addr bp.rsv.len bp.objCount) //
      result.size = bp.objCount ∧
      (∀ k (h_k : k < result.size) (h_src : k < bp.objCount),
        ElfBuildInvariant bp ⟨k, h_src⟩ (result[k]'h_k)) } := do
  let built ← buildFinFunction (n := bp.objCount)
    (β := fun i =>
      { eo : ElfOps bp.rsv.addr bp.rsv.len bp.objCount //
        ElfBuildInvariant bp i eo })
    (fun i => buildElf bp i)
  let arr : Array (ElfOps bp.rsv.addr bp.rsv.len bp.objCount) :=
    Array.ofFn fun i => (built i).val
  return ⟨arr, by simp [arr],
    by
      intro k h_k h_src
      let i : Fin bp.objCount := ⟨k, h_src⟩
      have h_get : arr[k]'h_k = (built i).val := by
        simp [arr, i]
      rw [h_get]
      exact (built i).property⟩

-- ============================================================================
-- buildLoadOps — assemble the full intrinsic-safe
-- `LoadOps` via `buildLoadElves`.
-- Cross-elf disjointness chains:
--   ElfBuildInvariant.mmap (each elf's segments[k].mmap = setupSegment …)
--   → setupSegment_mmap_eq (closed-form addr/len)
--   → BoundPlan.cross_elf_mmapRange_disjoint
-- The only `Except` failure path is `bakeReloc`'s 32-bit overflow.
-- ============================================================================

/-- Build the witnessed `LoadOps` tree. Fully constructive. The only `Except`
    failure path is `bakeReloc`'s 32-bit overflow check (psABI per-relocation
    `OVERFLOW_CHECK`); safety itself is established structurally, no decidable
    fallback. `build` packages this tree with proof-carrying user-code calls. -/
private def buildLoadOps (bp : BoundPlan) :
    Except String (LoadOps bp.rsv.addr bp.rsv.len bp.objCount) := do
  let ⟨elves, h_size, h_inv⟩ ← buildLoadElves bp
  let lo : LoadOps bp.rsv.addr bp.rsv.len bp.objCount :=
    { elfs := elves
      mmapsDisjoint := by
        -- Cross-elf mmap disjointness.
        intro i₁ i₂ h_i₁ h_i₂ h_lt k_i₁ k_i₂ h_k_i₁ h_k_i₂ m₁ m₂ h_m₁ h_m₂
        have h_i₁_n : i₁ < bp.objCount := by rw [h_size] at h_i₁; exact h_i₁
        have h_i₂_n : i₂ < bp.objCount := by rw [h_size] at h_i₂; exact h_i₂
        let fi₁ : Fin bp.objCount := ⟨i₁, h_i₁_n⟩
        let fi₂ : Fin bp.objCount := ⟨i₂, h_i₂_n⟩
        have h_inv₁ := h_inv i₁ h_i₁ h_i₁_n
        have h_inv₂ := h_inv i₂ h_i₂ h_i₂_n
        obtain ⟨h_size_eq₁, h_mmap_eq₁⟩ := h_inv₁
        obtain ⟨h_size_eq₂, h_mmap_eq₂⟩ := h_inv₂
        have h_k_src₁ : k_i₁ < (bp.elfAt fi₁).segmentCount := by
          rw [h_size_eq₁] at h_k_i₁; exact h_k_i₁
        have h_k_src₂ : k_i₂ < (bp.elfAt fi₂).segmentCount := by
          rw [h_size_eq₂] at h_k_i₂; exact h_k_i₂
        have h_mmap_su₁ : (setupSegment (bp.segAt fi₁ ⟨k_i₁, h_k_src₁⟩)
              (bp.handleAt fi₁) (bp.baseAt fi₁)).mmap = some m₁ := by
          rw [← h_mmap_eq₁ k_i₁ h_k_i₁ h_k_src₁]; exact h_m₁
        have h_mmap_su₂ : (setupSegment (bp.segAt fi₂ ⟨k_i₂, h_k_src₂⟩)
              (bp.handleAt fi₂) (bp.baseAt fi₂)).mmap = some m₂ := by
          rw [← h_mmap_eq₂ k_i₂ h_k_i₂ h_k_src₂]; exact h_m₂
        have ⟨h_a₁, h_l₁⟩ := setupSegment_mmap_eq (bp.segAt fi₁ ⟨k_i₁, h_k_src₁⟩)
          (bp.handleAt fi₁) (bp.baseAt fi₁) m₁ h_mmap_su₁
        have ⟨h_a₂, h_l₂⟩ := setupSegment_mmap_eq (bp.segAt fi₂ ⟨k_i₂, h_k_src₂⟩)
          (bp.handleAt fi₂) (bp.baseAt fi₂) m₂ h_mmap_su₂
        have h_disj := bp.cross_elf_mmapRange_disjoint fi₁ fi₂
          ⟨k_i₁, h_k_src₁⟩ ⟨k_i₂, h_k_src₂⟩ h_lt
        rw [h_a₁, h_l₁, h_a₂, h_l₂]; exact h_disj }
  return lo

-- ============================================================================
-- Ctor / dtor call resolution: init/fini call targets →
-- proof-carrying absolute call addresses.
-- ============================================================================

/-- Translate one target into its absolute call address. ET_DYN
    targets are base-relative (LeanLoad's only supported case);
    checked `Parse.parseFile` rejects ET_EXEC. -/
@[inline] private def callAddrOf (base target : UInt64) : UInt64 := base + target

-- ============================================================================
-- Call target in-exec-seg proof. The witness chain:
--   `Elf.callTargets.init` / `Elf.callTargets.fini` targets carry the executable-segment
--    witness → `ElfLayout.segmentsSegmentRangeEq` (the parallel
--    segment address-range bridge) → translate
--    `addr = base + target` into the matching exec PT_LOAD's runtime
--    bounds. The result lifts the checked-parse "in some exec PT_LOAD"
--    witness to a `BoundPlan`-relative claim ready for `CallOp`.
-- ============================================================================

/-- A target inside `[eaddr, eaddr + memsz)` of some `bp.elfAt i`'s
    `j`-th `SegmentLayout` is bounded by the page range, hence by
    `advance`, hence by the reservation. So `(base + target).toNat =
    base.toNat + target.toNat` doesn't wrap. -/
private theorem base_add_target_no_wrap (bp : BoundPlan)
    (i : Fin bp.objCount) (j : Fin (bp.elfAt i).segmentCount)
    (target : Eaddr)
    (h_hi : target.toNat < (bp.segAt i j).segment.eaddr.toNat +
                          (bp.segAt i j).segment.memsz.toNat) :
    (bp.baseAt i).toNat + target.toNat < 2 ^ 64 := by
  have h_no_wrap := bp.segment_pageRange_no_wrap i j
  have h_vm_le := (bp.segAt i j).vaddr_memsz_le_pageEnd
  have h_pe_le_adv : (bp.segAt i j).pageEndAddr.toNat ≤
      (bp.elfAt i).advance.toNat :=
    (bp.elfAt i).pageEndAddr_le_advance j
  have h_pe_eq := (bp.segAt i j).pageEndAddr_toNat
  have h_base_adv := bp.base_plus_advance_le_rsv_end i
  have h_rsv := bp.rsv.noWrap
  omega

/-- Lift one parse-stage callable-target witness through the chosen base address. -/
private theorem callTarget_addr_inExecSeg (bp : BoundPlan)
    (objectIdx : Fin bp.objCount)
    (target : Parse.CallTarget (bp.elfAt objectIdx).elf.segments)
    (h_ne : (Subtype.val target).val ≠ 0) :
    InExecSeg bp (callAddrOf (bp.baseAt objectIdx) (Subtype.val target).val) := by
  have h_in_exec := Subtype.property target
  rcases h_in_exec with h_zero | ⟨segIdx, h_segLt, h_exec, h_lo, h_hi⟩
  · exact absurd h_zero h_ne
  -- Bridge to SegmentLayout for the no-wrap argument.
  have h_segLt_eo : segIdx < (bp.elfAt objectIdx).segmentCount := h_segLt
  let segFin : Fin (bp.elfAt objectIdx).segmentCount := ⟨segIdx, h_segLt_eo⟩
  have h_segRangeEq := (bp.elfAt objectIdx).segmentsSegmentRangeEq segFin
  have h_exec_bp :
      ((bp.elfAt objectIdx).elf.segments.items[segIdx]'h_segLt).perm.exec = true := by
    simpa using h_exec
  have h_lo_bp :
      ((bp.elfAt objectIdx).elf.segments.items[segIdx]'h_segLt).eaddr.toNat ≤
        (Subtype.val target).toNat := by
    simpa using h_lo
  have h_hi_bp :
      (Subtype.val target).toNat <
        ((bp.elfAt objectIdx).elf.segments.items[segIdx]'h_segLt).eaddr.toNat +
          ((bp.elfAt objectIdx).elf.segments.items[segIdx]'h_segLt).memsz.toNat := by
    simpa using h_hi
  have h_hi_seg :
      (Subtype.val target).toNat <
        (bp.segAt objectIdx segFin).segment.eaddr.toNat +
          (bp.segAt objectIdx segFin).segment.memsz.toNat := by
    show (Subtype.val target).toNat <
      ((bp.elfAt objectIdx).segments[segFin]).segment.eaddr.toNat +
      ((bp.elfAt objectIdx).segments[segFin]).segment.memsz.toNat
    rw [h_segRangeEq.1, h_segRangeEq.2]
    exact h_hi_bp
  have h_no_wrap : (bp.baseAt objectIdx).toNat + (Subtype.val target).toNat < 2 ^ 64 :=
    base_add_target_no_wrap bp objectIdx segFin (Subtype.val target) h_hi_seg
  have h_addr_toNat :
      (callAddrOf (bp.baseAt objectIdx) (Subtype.val target).val).toNat =
        (bp.baseAt objectIdx).toNat + (Subtype.val target).toNat := by
    have h_no_wrap_val : (bp.baseAt objectIdx).toNat +
        (Subtype.val target).val.toNat < 2 ^ 64 := by
      simpa [Eaddr.toNat] using h_no_wrap
    unfold callAddrOf
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt h_no_wrap_val]
    simp [Eaddr.toNat]
  have h_old :
      ∃ (i : Fin bp.objCount) (j : Nat) (h : j < (bp.elfAt i).elf.segments.items.size),
        ((bp.elfAt i).elf.segments.items[j]'h).perm.exec = true ∧
        (bp.baseAt i).toNat + ((bp.elfAt i).elf.segments.items[j]'h).eaddr.toNat ≤
          (callAddrOf (bp.baseAt objectIdx) (Subtype.val target).val).toNat ∧
        (callAddrOf (bp.baseAt objectIdx) (Subtype.val target).val).toNat <
          (bp.baseAt i).toNat +
          ((bp.elfAt i).elf.segments.items[j]'h).eaddr.toNat +
          ((bp.elfAt i).elf.segments.items[j]'h).memsz.toNat :=
    ⟨objectIdx, segIdx, h_segLt, h_exec_bp,
      by rw [h_addr_toNat]; omega,
      by rw [h_addr_toNat]; omega⟩
  simpa [InExecSeg, BoundPlan.baseAt, BoundPlan.bases, BoundPlan.elfAt] using h_old

/-- Main-entry transfer address. Unlike init/fini arrays, zero is not a no-op for
    the final jump; reject it before touching runtime memory. -/
private def entryCall (bp : BoundPlan) : Except String (CallOp bp) :=
  let mainIdx : Fin bp.objCount := ⟨0, bp.n_pos⟩
  let target := (bp.elfAt mainIdx).elf.callTargets.entry
  if h_zero : (Subtype.val target).val = 0 then
    .error "finalize: main e_entry is zero; cannot transfer control"
  else
    .ok {
      addr := callAddrOf (bp.baseAt mainIdx) (Subtype.val target).val
      inExecSeg := callTarget_addr_inExecSeg bp mainIdx target h_zero }

/-- Collect proof-carrying calls from a per-elf array selector
    (`(·.callTargets.init)` for ctors, `(·.callTargets.fini)` for dtors),
    iterating elves in `order`. Walks the selected array forward.

    Zero targets are skipped — gabi leaves them unspecified, but historical
    practice (glibc / musl) treats them as no-ops. The filter is on the source
    target, not on the absolute `fnAddr`: for ET_DYN with nonzero base,
    `base + 0` is `base` (the elf's image start) which would be incorrectly
    emitted as a ctor address if we filtered after translation.

    `order : Array (Fin bp.objCount)` carries the bound at the type level;
    `bp.elfAt` and `bp.baseAt` are total — no `[]?` needed. -/
private def collectCalls (bp : BoundPlan) (order : Array (Fin bp.objCount))
    (arrOf : (elf : Elf) → Array (Parse.CallTarget elf.segments)) : Array (CallOp bp) :=
  order.flatMap fun objectIdx =>
    (arrOf (bp.elfAt objectIdx).elf).filterMap fun target =>
      let rawTarget : UInt64 := (Subtype.val target).val
      if h_ne : rawTarget != 0 then
        some {
          addr := callAddrOf (bp.baseAt objectIdx) rawTarget
          inExecSeg := by
            have h_ne' : (Subtype.val target).val ≠ 0 := by
              simpa [rawTarget] using (bne_iff_ne.mp h_ne)
            simpa [rawTarget] using callTarget_addr_inExecSeg bp objectIdx target h_ne' }
      else none

/-- Constructor calls with executable-segment witnesses attached. -/
private def ctorCalls (bp : BoundPlan) : Array (CallOp bp) :=
  collectCalls bp bp.initOrder.order (·.callTargets.init)

/-- Destructor calls with executable-segment witnesses attached. -/
private def dtorCalls (bp : BoundPlan) : Array (CallOp bp) :=
  collectCalls bp bp.initOrder.order.reverse (·.callTargets.fini)

/-- Complete pure finalization product: load ops plus all proof-carrying user-code
    transfers over the same bound plan. -/
def build (bp : BoundPlan) : Except String (Result bp) := do
  let loadOps ← buildLoadOps bp
  let entryCall ← entryCall bp
  return { loadOps, entryCall, ctorCalls := ctorCalls bp, dtorCalls := dtorCalls bp }

end LeanLoad.Finalize

/-
Builder: turn a `BasedPlan` into a safety-witnessed `LoadOps` tree
ready for `runSafe`.

Two top-level entry points:
  • `build`     — pure: `BasedPlan → safety-witnessed LoadOps`.
                  Returns a witnessed
                  `{ lo : LoadOps bp.n // Safe bp.rsv.addr bp.rsv.len lo }`.
                  `Safe` bundles the five flat safety predicates
                  (`MmapsDisjoint` + four `*Contained`). Construction
                  routes:
                    · Decidable instance on `Safe` — the runtime
                      check used today. Generic; works on any
                      `LoadOps`.
                    · Structural via `LoadOps.safe_of_LoadSafe`
                      (proven) — given a `LoadSafe` witness, derive
                      `Safe`. `LoadSafe` itself follows from
                      `BasedPlan`'s per-(i, j) theorems
                      (`segment_*_in_rsv`, `within_elf_*_disjoint`,
                      `cross_elf_*_disjoint`) once the buildCore-shape
                      lemma is in place. The flat→tree bridge for
                      `MmapsDisjoint` goes through
                      `List.pairwise_flatMap` + `pairwise_filterMap`.
  • `ctorAddrs` — pure: `BasedPlan → Array UInt64`. Resolves each
                  init-array entry through the per-elf base, in DFS
                  post-order; ET_DYN entries get the chosen base
                  added, ET_EXEC entries are absolute, zero entries
                  are skipped.

`Main.realize` consumes `build`'s witnessed result via
`LoadOps.runSafe`. There is no separate `safe` entry point.
-/

import LeanLoad.Materialize.LoadOps
import LeanLoad.Materialize.Reloc
import LeanLoad.Materialize.BasedPlan

namespace LeanLoad.Materialize

open LeanLoad
open LeanLoad.Plan (LoadPlan ElfPlan SegmentPlan)
open LeanLoad.Elaborate (Elf Formula)

-- ============================================================================
-- Builder: BasedPlan → LoadOps tree.
-- ============================================================================

-- ============================================================================
-- buildSegmentSafe — assemble one segment's `SegmentOps` together
-- with its `SegmentSafe` witness, in one shot. The witness is built
-- by chaining `setupSlots_*_eq` (closed forms of the slots) with the
-- matching `BasedPlan.segment_*_in_rsv` theorems. Stores come from
-- `bakeSegmentRelocs`; their bound is `bakeSegmentRelocs_storesInvariant`
-- with the universal predicate "byteLen ≤ 8 ∧ addr = base +
-- entry.r_offset for some entry whose `covered` witness gives
-- `segment_storeRange_in_rsv`".
-- ============================================================================

/-- Build one `SegmentOps` + its `SegmentSafe` witness + the
    `mmap_eq` equality that ties the built mmap back to its
    `setupSlots` source (needed by the enclosing `buildElfSegments`
    to chain to `within_elf_mmapRange_disjoint`). The only `Except`
    failure source is `bakeSegmentRelocs`'s 32-bit overflow check —
    safety itself is established structurally. -/
def buildSegmentSafe (bp : BasedPlan) (i : Nat) (h_i : i < bp.n)
    (j : Nat) (h_j : j < (bp.plan.load.elfs[i]'(by
      rw [bp.plan.load.elfs_size]; exact h_i)).segments.size) :
    Except String { so : SegmentOps bp.n //
      SegmentSafe bp.rsv.addr bp.rsv.len so ∧
      so.mmap =
        (setupSlots ((bp.plan.load.elfs[i]'(by
          rw [bp.plan.load.elfs_size]; exact h_i)).segments[j]'h_j)
          (bp.plan.objects.val[i]'h_i).handle
          (bp.bases[i]'(by rw [bp.bases_size]; exact h_i))).1 } := do
  have h_lp_i : i < bp.plan.load.elfs.size := by
    rw [bp.plan.load.elfs_size]; exact h_i
  let plan := bp.plan
  let elfs := plan.objectElfs
  let n := bp.n
  have h_elfs : elfs.size = n := plan.objectElfs_size
  have h_bases : bp.bases.size = elfs.size := bp.bases_size.trans h_elfs.symm
  have h_n_eq : n = elfs.size := h_elfs.symm
  let ep := plan.load.elfs[i]'h_lp_i
  let sp := ep.segments[j]'h_j
  let handle := (plan.objects.val[i]'h_i).handle
  let base := bp.bases[i]'(by rw [bp.bases_size]; exact h_i)
  -- Don't destructure `setupSlots` — keep the projection form so the
  -- characterisation lemmas (`setupSlots_*_eq`) align on the goal.
  let slots := setupSlots sp handle base
  let relocs : Array (Reloc.RelocEntry elfs.size sp.segment) := h_n_eq ▸ sp.relocs
  -- Use `match h_bake : ... with` to bind the bakeReloc equation so the
  -- storesInRange proof can invoke `bakeSegmentRelocs_storesInvariant`
  -- with the literal equation as `h_out`.
  match h_bake : bakeSegmentRelocs plan.formula elfs bp.bases h_bases base
                   sp.segment relocs with
  | .error e => .error e
  | .ok stores =>
    let so : SegmentOps n :=
      { plan := sp, mmap := slots.1, zero := slots.2.1,
        stores, mprotect := slots.2.2 }
    let h_safe : SegmentSafe bp.rsv.addr bp.rsv.len so := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- mmapInRange
        intro m h_m
        have ⟨h_addr, h_len⟩ := setupSlots_mmap_eq sp handle base m h_m
        rw [h_addr, h_len]
        exact bp.segment_mmapRange_in_rsv i h_i j h_j
      · -- zeroInRange
        intro z h_z
        have ⟨h_addr, h_len⟩ := setupSlots_zero_eq sp handle base z h_z
        rw [h_addr, h_len]
        exact bp.segment_zeroRange_in_rsv i h_i j h_j
      · -- storesInRange: every store came from some entry via `bakeReloc`,
        -- so `addr = base + entry.r_offset` and `byteLen ≤ 8`; combine
        -- with `entry.covered` and `segment_storeRange_in_rsv`.
        intro s h_s
        refine bakeSegmentRelocs_storesInvariant plan.formula elfs bp.bases
          h_bases base sp.segment relocs
          (fun s' => Runtime.InRange s'.addr s'.byteLen bp.rsv.addr bp.rsv.len)
          ?_ stores h_bake s h_s
        intro e s' h_br
        obtain ⟨h_addr, _h_size⟩ := bakeReloc_ok_some plan.formula elfs bp.bases
          h_bases base sp.segment e s' h_br
        have h_byteLen := bakeReloc_byteLen_le_8 plan.formula elfs bp.bases
          h_bases base sp.segment e s' h_br
        rw [h_addr]
        exact bp.segment_storeRange_in_rsv i h_i j h_j e.r_offset e.covered
          s'.byteLen h_byteLen
      · -- mprotectInRange — mprotect is at (base + pageVaddr, pageLength).
        have ⟨h_addr, h_len⟩ := setupSlots_mprotect_eq sp handle base
        rw [show so.mprotect = slots.2.2 from rfl, h_addr, h_len]
        exact bp.segment_mprotectRange_in_rsv i h_i j h_j
    -- The `mmap_eq` field — `so.mmap = slots.1` by construction (rfl).
    .ok ⟨so, h_safe, rfl⟩

-- ============================================================================
-- buildElfSegments — recursive helper that builds an elf's segment
-- array, threading through the per-index `mmap_eq` invariant so the
-- within-elf disjointness proof can chain to
-- `within_elf_mmapRange_disjoint`. The recursion is on `segIdx`,
-- counting down from `ep.segments.size`.
--
-- The invariants carried by the accumulator:
--   • `acc.size = segIdx`
--   • every previously-built segment is `SegmentSafe`.
--   • every previously-built segment's mmap matches the corresponding
--     `setupSlots` output.
-- ============================================================================

private def buildElfSegmentsAux (bp : BasedPlan) (i : Nat) (h_i : i < bp.n)
    (h_lp_i : i < bp.plan.load.elfs.size)
    (segIdx : Nat)
    (h_segIdx : segIdx ≤ (bp.plan.load.elfs[i]'h_lp_i).segments.size)
    (acc : Array (SegmentOps bp.n))
    (h_size : acc.size = segIdx)
    (h_safe : ∀ k (h_k : k < acc.size),
      SegmentSafe bp.rsv.addr bp.rsv.len (acc[k]'h_k))
    (h_mmap : ∀ k (h_k : k < acc.size)
      (h_src : k < (bp.plan.load.elfs[i]'h_lp_i).segments.size),
      (acc[k]'h_k).mmap =
        (setupSlots ((bp.plan.load.elfs[i]'h_lp_i).segments[k]'h_src)
          (bp.plan.objects.val[i]'h_i).handle
          (bp.bases[i]'(by rw [bp.bases_size]; exact h_i))).1) :
    Except String { result : Array (SegmentOps bp.n) //
      result.size = (bp.plan.load.elfs[i]'h_lp_i).segments.size ∧
      (∀ k (h_k : k < result.size),
        SegmentSafe bp.rsv.addr bp.rsv.len (result[k]'h_k)) ∧
      (∀ k (h_k : k < result.size)
        (h_src : k < (bp.plan.load.elfs[i]'h_lp_i).segments.size),
        (result[k]'h_k).mmap =
          (setupSlots ((bp.plan.load.elfs[i]'h_lp_i).segments[k]'h_src)
            (bp.plan.objects.val[i]'h_i).handle
            (bp.bases[i]'(by rw [bp.bases_size]; exact h_i))).1) } := by
  exact
    if h_done : segIdx = (bp.plan.load.elfs[i]'h_lp_i).segments.size then
      .ok ⟨acc, h_done ▸ h_size, h_safe, h_mmap⟩
    else by
      have h_lt : segIdx < (bp.plan.load.elfs[i]'h_lp_i).segments.size :=
        Nat.lt_of_le_of_ne h_segIdx h_done
      exact do
        let ⟨so, h_so_safe, h_so_mmap⟩ ← buildSegmentSafe bp i h_i segIdx h_lt
        let acc' := acc.push so
        have h_size' : acc'.size = segIdx + 1 := by
          show (acc.push so).size = segIdx + 1
          rw [Array.size_push, h_size]
        have h_safe' : ∀ k (h_k : k < acc'.size),
            SegmentSafe bp.rsv.addr bp.rsv.len (acc'[k]'h_k) := by
          intro k h_k
          have h_k_split : k < acc.size ∨ k = acc.size := by
            rw [Array.size_push] at h_k; omega
          rcases h_k_split with h_k_lt | h_k_eq
          · have : acc'[k]'h_k = acc[k]'h_k_lt := by
              show (acc.push so)[k]'h_k = _
              rw [Array.getElem_push, dif_pos h_k_lt]
            rw [this]; exact h_safe k h_k_lt
          · subst h_k_eq
            have : acc'[acc.size]'h_k = so := by
              show (acc.push so)[acc.size]'h_k = so
              rw [Array.getElem_push, dif_neg (Nat.lt_irrefl _)]
            rw [this]; exact h_so_safe
        have h_mmap' : ∀ k (h_k : k < acc'.size)
            (h_src : k < (bp.plan.load.elfs[i]'h_lp_i).segments.size),
            (acc'[k]'h_k).mmap =
              (setupSlots ((bp.plan.load.elfs[i]'h_lp_i).segments[k]'h_src)
                (bp.plan.objects.val[i]'h_i).handle
                (bp.bases[i]'(by rw [bp.bases_size]; exact h_i))).1 := by
          intro k h_k h_src
          have h_k_split : k < acc.size ∨ k = acc.size := by
            rw [Array.size_push] at h_k; omega
          rcases h_k_split with h_k_lt | h_k_eq
          · have : acc'[k]'h_k = acc[k]'h_k_lt := by
              show (acc.push so)[k]'h_k = _
              rw [Array.getElem_push, dif_pos h_k_lt]
            rw [this]; exact h_mmap k h_k_lt h_src
          · subst h_k_eq
            have h_seg_eq : acc.size = segIdx := h_size
            have : acc'[acc.size]'h_k = so := by
              show (acc.push so)[acc.size]'h_k = so
              rw [Array.getElem_push, dif_neg (Nat.lt_irrefl _)]
            rw [this]
            -- The source segment is at index acc.size = segIdx.
            -- We have h_so_mmap with index segIdx.
            have h_seg_index :
                (bp.plan.load.elfs[i]'h_lp_i).segments[acc.size]'h_src =
                (bp.plan.load.elfs[i]'h_lp_i).segments[segIdx]'h_lt := by
              congr 1
            rw [h_seg_index]; exact h_so_mmap
        buildElfSegmentsAux bp i h_i h_lp_i (segIdx + 1) h_lt acc' h_size'
          h_safe' h_mmap'
termination_by (bp.plan.load.elfs[i]'h_lp_i).segments.size - segIdx
decreasing_by omega

/-- Build an elf's segments array with per-index `SegmentSafe` and
    `mmap_eq` invariants. The wrapper for `buildElfSegmentsAux`. -/
def buildElfSegments (bp : BasedPlan) (i : Nat) (h_i : i < bp.n)
    (h_lp_i : i < bp.plan.load.elfs.size) :
    Except String { result : Array (SegmentOps bp.n) //
      result.size = (bp.plan.load.elfs[i]'h_lp_i).segments.size ∧
      (∀ k (h_k : k < result.size),
        SegmentSafe bp.rsv.addr bp.rsv.len (result[k]'h_k)) ∧
      (∀ k (h_k : k < result.size)
        (h_src : k < (bp.plan.load.elfs[i]'h_lp_i).segments.size),
        (result[k]'h_k).mmap =
          (setupSlots ((bp.plan.load.elfs[i]'h_lp_i).segments[k]'h_src)
            (bp.plan.objects.val[i]'h_i).handle
            (bp.bases[i]'(by rw [bp.bases_size]; exact h_i))).1) } :=
  buildElfSegmentsAux bp i h_i h_lp_i 0 (Nat.zero_le _) #[]
    rfl
    (by intro k h_k; exact absurd h_k (by simp))
    (by intro k h_k _; exact absurd h_k (by simp))

-- ============================================================================
-- buildElfSafe — assemble one elf's `ElfOps` + its `ElfSafe` witness.
-- Within-elf disjointness chains `mmap_eq` (segment k's built mmap
-- matches setupSlots's output) with `setupSlots_mmap_eq` (closed form
-- of (addr, len)) into `within_elf_mmapRange_disjoint`'s conclusion.
-- ============================================================================

/-- Build one `ElfOps` + its `ElfSafe` witness. -/
def buildElfSafe (bp : BasedPlan) (i : Nat) (h_i : i < bp.n) :
    Except String { eo : ElfOps bp.n //
      ElfSafe bp.rsv.addr bp.rsv.len eo } := do
  have h_lp_i : i < bp.plan.load.elfs.size := by
    rw [bp.plan.load.elfs_size]; exact h_i
  let ⟨segments, h_size, h_safe, h_mmap⟩ ← buildElfSegments bp i h_i h_lp_i
  let base := bp.bases[i]'(by rw [bp.bases_size]; exact h_i)
  let handle := (bp.plan.objects.val[i]'h_i).handle
  let ep := bp.plan.load.elfs[i]'h_lp_i
  let eo : ElfOps bp.n := { base, segments }
  let h_elfSafe : ElfSafe bp.rsv.addr bp.rsv.len eo := by
    refine ⟨?_, ?_⟩
    · -- Each segment is SegmentSafe.
      intro k h_k; exact h_safe k h_k
    · -- Within-elf mmap disjointness: for j₁ < j₂, both segments' mmaps
      -- come from setupSlots on the corresponding source segments.
      intro j₁ j₂ h_j₁ h_j₂ h_lt m₁ m₂ h_m₁ h_m₂
      have h_j₁_src : j₁ < ep.segments.size := by rw [h_size] at h_j₁; exact h_j₁
      have h_j₂_src : j₂ < ep.segments.size := by rw [h_size] at h_j₂; exact h_j₂
      -- mmap_eq says: segments[j].mmap = (setupSlots ep.segments[j] _ _).1.
      have h_mmap_eq₁ := h_mmap j₁ h_j₁ h_j₁_src
      have h_mmap_eq₂ := h_mmap j₂ h_j₂ h_j₂_src
      -- segments[j₁].mmap = some m₁, so (setupSlots …).1 = some m₁.
      have h_su₁ : (setupSlots (ep.segments[j₁]'h_j₁_src) handle base).1 = some m₁ := by
        rw [← h_mmap_eq₁]; exact h_m₁
      have h_su₂ : (setupSlots (ep.segments[j₂]'h_j₂_src) handle base).1 = some m₂ := by
        rw [← h_mmap_eq₂]; exact h_m₂
      -- Extract m₁, m₂'s addr/len via setupSlots_mmap_eq.
      have ⟨h_a₁, h_l₁⟩ := setupSlots_mmap_eq (ep.segments[j₁]'h_j₁_src) handle base m₁ h_su₁
      have ⟨h_a₂, h_l₂⟩ := setupSlots_mmap_eq (ep.segments[j₂]'h_j₂_src) handle base m₂ h_su₂
      -- Apply the within-elf disjointness.
      have h_disj := bp.within_elf_mmapRange_disjoint i h_i j₁ j₂ h_j₁_src h_j₂_src h_lt
      -- Rewrite m₁'s and m₂'s addr/len in the goal.
      rw [h_a₁, h_l₁, h_a₂, h_l₂]
      exact h_disj
  return ⟨eo, h_elfSafe⟩

-- ============================================================================
-- buildLoadElves — recursive helper that builds the array of ElfOps,
-- threading through per-elf invariants for cross-elf disjointness.
--
-- For each pair of distinct elves at indices i₁ < i₂, both elves'
-- segments have their mmap matching the setupSlots output; the cross-
-- elf disjointness then follows from `cross_elf_mmapRange_disjoint`.
-- ============================================================================

/-- Per-elf invariant: each elf's segments match buildElfSegments's
    output (i.e. their mmaps come from setupSlots on the source
    segments). Used to thread cross-elf disjointness. -/
private def ElfBuildInvariant (bp : BasedPlan) (i : Nat) (h_i : i < bp.n)
    (eo : ElfOps bp.n) : Prop :=
  let h_lp_i : i < bp.plan.load.elfs.size := by
    rw [bp.plan.load.elfs_size]; exact h_i
  eo.base = bp.bases[i]'(by rw [bp.bases_size]; exact h_i) ∧
  eo.segments.size = (bp.plan.load.elfs[i]'h_lp_i).segments.size ∧
  (∀ k (h_k : k < eo.segments.size)
    (h_src : k < (bp.plan.load.elfs[i]'h_lp_i).segments.size),
    (eo.segments[k]'h_k).mmap =
      (setupSlots ((bp.plan.load.elfs[i]'h_lp_i).segments[k]'h_src)
        (bp.plan.objects.val[i]'h_i).handle
        (bp.bases[i]'(by rw [bp.bases_size]; exact h_i))).1)

/-- Build one `ElfOps` + its `ElfSafe` witness + `ElfBuildInvariant`.
    Extended version of `buildElfSafe` that exposes the structural
    invariant needed for cross-elf disjointness. -/
def buildElfSafeFull (bp : BasedPlan) (i : Nat) (h_i : i < bp.n) :
    Except String { eo : ElfOps bp.n //
      ElfSafe bp.rsv.addr bp.rsv.len eo ∧
      ElfBuildInvariant bp i h_i eo } := do
  have h_lp_i : i < bp.plan.load.elfs.size := by
    rw [bp.plan.load.elfs_size]; exact h_i
  let ⟨segments, h_size, h_safe, h_mmap⟩ ← buildElfSegments bp i h_i h_lp_i
  let base := bp.bases[i]'(by rw [bp.bases_size]; exact h_i)
  let handle := (bp.plan.objects.val[i]'h_i).handle
  let ep := bp.plan.load.elfs[i]'h_lp_i
  let eo : ElfOps bp.n := { base, segments }
  let h_elfSafe : ElfSafe bp.rsv.addr bp.rsv.len eo := by
    refine ⟨?_, ?_⟩
    · intro k h_k; exact h_safe k h_k
    · intro j₁ j₂ h_j₁ h_j₂ h_lt m₁ m₂ h_m₁ h_m₂
      have h_j₁_src : j₁ < ep.segments.size := by rw [h_size] at h_j₁; exact h_j₁
      have h_j₂_src : j₂ < ep.segments.size := by rw [h_size] at h_j₂; exact h_j₂
      have h_mmap_eq₁ := h_mmap j₁ h_j₁ h_j₁_src
      have h_mmap_eq₂ := h_mmap j₂ h_j₂ h_j₂_src
      have h_su₁ : (setupSlots (ep.segments[j₁]'h_j₁_src) handle base).1 = some m₁ := by
        rw [← h_mmap_eq₁]; exact h_m₁
      have h_su₂ : (setupSlots (ep.segments[j₂]'h_j₂_src) handle base).1 = some m₂ := by
        rw [← h_mmap_eq₂]; exact h_m₂
      have ⟨h_a₁, h_l₁⟩ := setupSlots_mmap_eq (ep.segments[j₁]'h_j₁_src) handle base m₁ h_su₁
      have ⟨h_a₂, h_l₂⟩ := setupSlots_mmap_eq (ep.segments[j₂]'h_j₂_src) handle base m₂ h_su₂
      have h_disj := bp.within_elf_mmapRange_disjoint i h_i j₁ j₂ h_j₁_src h_j₂_src h_lt
      rw [h_a₁, h_l₁, h_a₂, h_l₂]; exact h_disj
  let h_inv : ElfBuildInvariant bp i h_i eo :=
    ⟨rfl, h_size, h_mmap⟩
  return ⟨eo, h_elfSafe, h_inv⟩

private def buildLoadElvesAux (bp : BasedPlan)
    (elfIdx : Nat) (h_elfIdx : elfIdx ≤ bp.n)
    (acc : Array (ElfOps bp.n))
    (h_size : acc.size = elfIdx)
    (h_safe : ∀ k (h_k : k < acc.size),
      ElfSafe bp.rsv.addr bp.rsv.len (acc[k]'h_k))
    (h_inv : ∀ k (h_k : k < acc.size) (h_src : k < bp.n),
      ElfBuildInvariant bp k h_src (acc[k]'h_k)) :
    Except String { result : Array (ElfOps bp.n) //
      result.size = bp.n ∧
      (∀ k (h_k : k < result.size),
        ElfSafe bp.rsv.addr bp.rsv.len (result[k]'h_k)) ∧
      (∀ k (h_k : k < result.size) (h_src : k < bp.n),
        ElfBuildInvariant bp k h_src (result[k]'h_k)) } := by
  exact
    if h_done : elfIdx = bp.n then
      .ok ⟨acc, h_done ▸ h_size, h_safe, h_inv⟩
    else by
      have h_lt : elfIdx < bp.n := Nat.lt_of_le_of_ne h_elfIdx h_done
      exact do
        let ⟨eo, h_eoSafe, h_eoInv⟩ ← buildElfSafeFull bp elfIdx h_lt
        let acc' := acc.push eo
        have h_size' : acc'.size = elfIdx + 1 := by
          show (acc.push eo).size = elfIdx + 1
          rw [Array.size_push, h_size]
        have h_safe' : ∀ k (h_k : k < acc'.size),
            ElfSafe bp.rsv.addr bp.rsv.len (acc'[k]'h_k) := by
          intro k h_k
          have h_k_split : k < acc.size ∨ k = acc.size := by
            rw [Array.size_push] at h_k; omega
          rcases h_k_split with h_k_lt | h_k_eq
          · have : acc'[k]'h_k = acc[k]'h_k_lt := by
              show (acc.push eo)[k]'h_k = _
              rw [Array.getElem_push, dif_pos h_k_lt]
            rw [this]; exact h_safe k h_k_lt
          · subst h_k_eq
            have : acc'[acc.size]'h_k = eo := by
              show (acc.push eo)[acc.size]'h_k = eo
              rw [Array.getElem_push, dif_neg (Nat.lt_irrefl _)]
            rw [this]; exact h_eoSafe
        have h_inv' : ∀ k (h_k : k < acc'.size) (h_src : k < bp.n),
            ElfBuildInvariant bp k h_src (acc'[k]'h_k) := by
          intro k h_k h_src
          have h_k_split : k < acc.size ∨ k = acc.size := by
            rw [Array.size_push] at h_k; omega
          rcases h_k_split with h_k_lt | h_k_eq
          · have : acc'[k]'h_k = acc[k]'h_k_lt := by
              show (acc.push eo)[k]'h_k = _
              rw [Array.getElem_push, dif_pos h_k_lt]
            rw [this]; exact h_inv k h_k_lt h_src
          · subst h_k_eq
            have h_seg_eq : acc.size = elfIdx := h_size
            have : acc'[acc.size]'h_k = eo := by
              show (acc.push eo)[acc.size]'h_k = eo
              rw [Array.getElem_push, dif_neg (Nat.lt_irrefl _)]
            rw [this]
            -- h_eoInv is for index elfIdx; h_src is for k = acc.size = elfIdx.
            have h_idx_eq : acc.size = elfIdx := h_size
            -- Need to argue ElfBuildInvariant bp k h_src eo, where k = acc.size, h_src : k < bp.n.
            -- We have h_eoInv : ElfBuildInvariant bp elfIdx h_lt eo.
            -- Since k = acc.size = elfIdx, these are equal (modulo proof
            -- irrelevance on h_src).
            have h_k_eq_elfIdx : (acc.size : Nat) = elfIdx := h_idx_eq
            rw [show h_src =
              (h_k_eq_elfIdx ▸ h_lt : acc.size < bp.n) from rfl]
            exact h_k_eq_elfIdx ▸ h_eoInv
        buildLoadElvesAux bp (elfIdx + 1) h_lt acc' h_size' h_safe' h_inv'
termination_by bp.n - elfIdx
decreasing_by omega

/-- Build all elves with `ElfSafe` + `ElfBuildInvariant` witnesses. -/
def buildLoadElves (bp : BasedPlan) :
    Except String { result : Array (ElfOps bp.n) //
      result.size = bp.n ∧
      (∀ k (h_k : k < result.size),
        ElfSafe bp.rsv.addr bp.rsv.len (result[k]'h_k)) ∧
      (∀ k (h_k : k < result.size) (h_src : k < bp.n),
        ElfBuildInvariant bp k h_src (result[k]'h_k)) } :=
  buildLoadElvesAux bp 0 (Nat.zero_le _) #[] rfl
    (by intro k h_k; exact absurd h_k (by simp))
    (by intro k h_k _; exact absurd h_k (by simp))

private def buildCore (bp : BasedPlan) :
    Except String (LoadOps bp.n) := do
  let plan := bp.plan
  let lp := plan.load
  let elfs := plan.objectElfs
  let formula := plan.formula
  let n := bp.n
  have h_elfs    : elfs.size    = n := plan.objectElfs_size
  have h_lp_elfs : lp.elfs.size = n := lp.elfs_size
  let bases := bp.bases
  have h_bases_n : bases.size = n := bp.bases_size
  have h_bases : bases.size = elfs.size := h_bases_n.trans h_elfs.symm
  have h_n_eq : n = elfs.size := h_elfs.symm
  let mut lo : Array (ElfOps n) := #[]
  for h : i in [:lp.elfs.size] do
    let ep := lp.elfs[i]
    have hi_n : i < n := by rw [← h_lp_elfs]; exact h.upper
    let handle := (plan.objects.val[i]'hi_n).handle
    let base := bases[i]'(by rw [h_bases_n]; exact hi_n)
    let mut segments : Array (SegmentOps n) := #[]
    for h2 : segI in [:ep.segments.size] do
      let sp := ep.segments[segI]
      let (mmap, zero, mprotect) := setupSlots sp handle base
      -- `sp.relocs : Array (RelocEntry n sp.segment)`; bakeSegmentRelocs
      -- wants `Array (RelocEntry elfs.size sp.segment)`. Rewriting
      -- along `n = elfs.size` preserves the segment parameter.
      let relocs : Array (Reloc.RelocEntry elfs.size sp.segment) :=
        h_n_eq ▸ sp.relocs
      let stores ←
        bakeSegmentRelocs formula elfs bases h_bases base sp.segment relocs
      segments := segments.push
        { plan := sp, mmap, zero, stores, mprotect }
    lo := lo.push { base, segments }
  return lo

/-- Witnessed build: assemble the `LoadOps` tree and gate it through
    the five decidable safety predicates
    (`MmapsDisjoint` / `*Contained`) parameterised on the reservation
    `[bp.rsv.addr, +bp.rsv.len)`.

    Returns the witnessed tree on success. Failure means a planner
    bug (the OS would otherwise raise SIGSEGV / mmap failure); the
    body of the proof discharge is residual — see file docstring.

    Callers consume the result via `LoadOps.runSafe`. -/
def build (bp : BasedPlan) :
    Except String { lo : LoadOps bp.n // Safe bp.rsv.addr bp.rsv.len lo } := do
  let lo ← buildCore bp
  if h : Safe bp.rsv.addr bp.rsv.len lo then
    .ok ⟨lo, h⟩
  else
    .error "Materialize.build: planned ops violate safety invariants \
      (loader bug — mmaps collide or extend outside the reservation)"

-- ============================================================================
-- Ctor / dtor address resolution: init-array / fini-array entries →
-- flat absolute addresses.
-- ============================================================================

/-- Collect function addresses to call, from a per-elf array selector
    (`(·.initArr)` for ctors, `(·.finiArr)` for dtors), iterating elves
    in `order`. Walks the selected array forward.

    For each elf, each entry's runtime address is: ET_DYN entries get
    the chosen base added; ET_EXEC entries are absolute. Zero entries
    are skipped — gabi leaves them unspecified, but historical
    practice (where zero-terminators are common) treats them as
    no-ops.

    `order : Array (Fin n)` carries the bound at the type level; both
    `lp.elfs[…]` and `bases[…]` are total — no `[]?` needed. -/
def collectAddrs (lp : LoadPlan n) (bases : Array UInt64)
    (h_bases : bases.size = n) (order : Array (Fin n))
    (arrOf : Elaborate.Elf → Array UInt64) : Array UInt64 :=
  Id.run do
    let mut addrs : Array UInt64 := #[]
    for objectIdx in order do
      let ep   := lp.elfs[objectIdx.val]'(by rw [lp.elfs_size]; exact objectIdx.isLt)
      let base := bases[objectIdx.val]'(by rw [h_bases]; exact objectIdx.isLt)
      let isExec := ep.elf.elfType == .exec
      for entry in arrOf ep.elf do
        let fnAddr := if isExec then entry else base + entry
        if fnAddr != 0 then addrs := addrs.push fnAddr
    return addrs

/-- Constructor (`DT_INIT_ARRAY`) addresses, in DFS post-order. -/
def ctorAddrs (bp : BasedPlan) : Array UInt64 :=
  collectAddrs bp.plan.load bp.bases bp.bases_size bp.plan.initOrder (·.initArr)

/-- Destructor (`DT_FINI_ARRAY`) addresses, in *reverse* DFS post-order
    so deepest-dep fini runs after shallower fini, mirroring init's
    "deps first" order. gabi 08 mandates a partial order; reverse-init
    is glibc / musl's conventional choice. -/
def dtorAddrs (bp : BasedPlan) : Array UInt64 :=
  collectAddrs bp.plan.load bp.bases bp.bases_size
    bp.plan.initOrder.reverse (·.finiArr)

end LeanLoad.Materialize

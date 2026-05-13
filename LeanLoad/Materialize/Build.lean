/-
Builder: turn a `BasedPlan` into a safety-witnessed `LoadOps` tree
ready for `runSafe`. Fully constructive — no decidable safety
fallback, no `.error` branch for safety.

Two top-level entry points:
  • `build`     — pure: `BasedPlan → safety-witnessed LoadOps`.
                  Returns `{ lo : LoadOps bp.n // Safe … lo }`. The
                  `Safe` witness is built structurally:
                    1. `buildSegmentSafe` per segment — combines
                       `setupSlots_*_eq` (closed form of (addr, len))
                       with `BasedPlan.segment_*_in_rsv` (per-slot
                       InRange) and `bakeReloc` characterisation +
                       `bakeSegmentRelocs_storesInvariant`.
                    2. `buildElfSafe` per elf — assembles
                       `buildElfSegments`'s output + within-elf
                       disjointness from
                       `BasedPlan.within_elf_mmapRange_disjoint`.
                    3. `buildLoadElves` across elves — threads
                       `ElfBuildInvariant` so the cross-elf
                       disjointness in `buildSafe` can chain to
                       `BasedPlan.cross_elf_mmapRange_disjoint`.
                    4. `safe_of_LoadSafe` bridges `LoadSafe → Safe`
                       (4 contained bridges + 1 disjoint bridge via
                       `List.pairwise_flatMap` + `pairwise_filterMap`).
                  The only `Except` failure path is `bakeReloc`'s
                  32-bit overflow check (psABI per-relocation
                  `OVERFLOW_CHECK`).
  • `ctorAddrs` — pure: `BasedPlan → Array UInt64`. Resolves each
                  init-array entry through the per-elf base, in DFS
                  post-order; ET_DYN entries get the chosen base
                  added, ET_EXEC entries are absolute, zero entries
                  are skipped.

`Main.realize` consumes `build`'s witnessed result via
`LoadOps.runSafe`. There is no separate `safe` entry point.

The two recursive constructions (segments-of-an-elf, elves-of-the-
load) share one generic helper, `buildSafeArray`: given a `count`
and a per-index `Except`-returning step, it threads a per-index
invariant `P k b` through `count` push extensions. Both
`buildElfSegments` and `buildLoadElves` are thin wrappers — the
push-extension proof obligations live in `buildSafeArrayAux` only.
-/

import LeanLoad.Materialize.LoadOps
import LeanLoad.Materialize.Reloc
import LeanLoad.Materialize.BasedPlan

namespace LeanLoad.Materialize

open LeanLoad
open LeanLoad.Plan (LoadPlan ElfPlan SegmentPlan)
open LeanLoad.Elaborate (Elf Formula)

-- ============================================================================
-- buildSafeArray — generic helper for "build an array of `count`
-- elements, each satisfying a per-index invariant `P k b`". Used by
-- `buildElfSegments` (segments-of-an-elf) and `buildLoadElves`
-- (elves-of-the-load). Both were nearly-identical 70-line aux
-- functions before extraction.
-- ============================================================================

/-- Recursive helper for `buildSafeArray`. The accumulator carries:
    `acc.size = idx` and the per-index invariant for every already-
    built element. Each iteration steps `idx → idx + 1` by pushing one
    element built via `step idx`. -/
private def buildSafeArrayAux {β : Type} (count : Nat) (P : Nat → β → Prop)
    (step : (k : Nat) → k < count → Except String { b : β // P k b })
    (idx : Nat) (h_idx : idx ≤ count)
    (acc : Array β)
    (h_size : acc.size = idx)
    (h_acc : ∀ k (h_k : k < acc.size), P k (acc[k]'h_k)) :
    Except String { arr : Array β // arr.size = count ∧
      ∀ k (h_k : k < arr.size), P k (arr[k]'h_k) } := by
  exact
    if h_done : idx = count then
      .ok ⟨acc, h_done ▸ h_size, h_acc⟩
    else by
      have h_lt : idx < count := Nat.lt_of_le_of_ne h_idx h_done
      exact do
        let ⟨b, h_pb⟩ ← step idx h_lt
        let acc' := acc.push b
        have h_size' : acc'.size = idx + 1 := by
          show (acc.push b).size = idx + 1
          rw [Array.size_push, h_size]
        have h_acc' : ∀ k (h_k : k < acc'.size), P k (acc'[k]'h_k) := by
          intro k h_k
          have h_split : k < acc.size ∨ k = acc.size := by
            rw [Array.size_push] at h_k; omega
          rcases h_split with h_k_lt | h_k_eq
          · have : acc'[k]'h_k = acc[k]'h_k_lt := by
              show (acc.push b)[k]'h_k = _
              rw [Array.getElem_push, dif_pos h_k_lt]
            rw [this]; exact h_acc k h_k_lt
          · subst h_k_eq
            have h_get : acc'[acc.size]'h_k = b := by
              show (acc.push b)[acc.size]'h_k = b
              rw [Array.getElem_push, dif_neg (Nat.lt_irrefl _)]
            rw [h_get, show acc.size = idx from h_size]; exact h_pb
        buildSafeArrayAux count P step (idx + 1) h_lt acc' h_size' h_acc'
termination_by count - idx
decreasing_by omega

/-- Build an array of `count` elements where each element at index
    `k` satisfies the predicate `P k`. The caller provides a `step`
    that — given the index `k` and its bound — produces one element
    with its witness, or fails with a string error.

    Returns the array together with `arr.size = count` and a pointwise
    proof `∀ k h_k, P k (arr[k]'h_k)`.

    Used by `buildElfSegments` and `buildLoadElves`. -/
def buildSafeArray {β : Type} (count : Nat) (P : Nat → β → Prop)
    (step : (k : Nat) → k < count → Except String { b : β // P k b }) :
    Except String { arr : Array β // arr.size = count ∧
      ∀ k (h_k : k < arr.size), P k (arr[k]'h_k) } :=
  buildSafeArrayAux count P step 0 (Nat.zero_le _) #[] rfl
    (by intro k h_k; exact absurd h_k (by simp))

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
def buildSegmentSafe (bp : BasedPlan) (i : Fin bp.n)
    (j : Fin (bp.elfAt i).segments.size) :
    Except String { so : SegmentOps bp.n //
      SegmentSafe bp.rsv.addr bp.rsv.len so ∧
      so.mmap =
        (setupSlots (bp.segAt i j) (bp.handleAt i) (bp.baseAt i)).1 } := do
  let plan := bp.plan
  let elfs := plan.objectElfs
  let n := bp.n
  have h_elfs : elfs.size = n := plan.objectElfs_size
  have h_bases : bp.bases.size = elfs.size := bp.bases_size.trans h_elfs.symm
  have h_n_eq : n = elfs.size := h_elfs.symm
  let sp := bp.segAt i j
  let handle := bp.handleAt i
  let base := bp.baseAt i
  -- Don't destructure `setupSlots` — keep the projection form so the
  -- characterisation lemmas (`setupSlots_*_eq`) align on the goal.
  let slots := setupSlots sp handle base
  let relocs : Array (Plan.Reloc.RelocEntry elfs.size sp.segment) :=
    h_n_eq ▸ sp.relocs
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
        exact bp.segment_mmapRange_in_rsv i j
      · -- zeroInRange
        intro z h_z
        have ⟨h_addr, h_len⟩ := setupSlots_zero_eq sp handle base z h_z
        rw [h_addr, h_len]
        exact bp.segment_zeroRange_in_rsv i j
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
        exact bp.segment_storeRange_in_rsv i j e.r_offset e.covered
          s'.byteLen h_byteLen
      · -- mprotectInRange — mprotect is at (base + pageVaddr, pageLength).
        have ⟨h_addr, h_len⟩ := setupSlots_mprotect_eq sp handle base
        rw [show so.mprotect = slots.2.2 from rfl, h_addr, h_len]
        exact bp.segment_mprotectRange_in_rsv i j
    -- The `mmap_eq` field — `so.mmap = slots.1` by construction (rfl).
    .ok ⟨so, h_safe, rfl⟩

-- ============================================================================
-- buildElfSegments — build an elf's segment array with per-index
-- `SegmentSafe` and `mmap_eq` invariants. A thin wrapper over
-- `buildSafeArray` — the combined predicate `(SegmentSafe ∧
-- mmap_eq)` is unzipped on return for caller convenience.
-- ============================================================================

/-- Build an elf's segments array with per-index `SegmentSafe` and
    `mmap_eq` invariants. The `mmap_eq` invariant lets
    `buildElfSafe` chain to `within_elf_mmapRange_disjoint`. -/
def buildElfSegments (bp : BasedPlan) (i : Fin bp.n) :
    Except String { result : Array (SegmentOps bp.n) //
      result.size = (bp.elfAt i).segments.size ∧
      (∀ k (h_k : k < result.size),
        SegmentSafe bp.rsv.addr bp.rsv.len (result[k]'h_k)) ∧
      (∀ k (h_k : k < result.size)
        (h_src : k < (bp.elfAt i).segments.size),
        (result[k]'h_k).mmap =
          (setupSlots (bp.segAt i ⟨k, h_src⟩) (bp.handleAt i) (bp.baseAt i)).1) } := do
  -- Combined predicate: SegmentSafe ∧ (bound-discharged) mmap_eq.
  -- The mmap_eq clause is wrapped in `∀ h_src` so the step's bound
  -- proof can produce it for any equal-by-proof-irrelevance witness.
  let ⟨arr, h_size, h_p⟩ ← buildSafeArray (bp.elfAt i).segments.size
    (fun k so =>
      SegmentSafe bp.rsv.addr bp.rsv.len so ∧
      ∀ (h_src : k < (bp.elfAt i).segments.size),
        so.mmap = (setupSlots (bp.segAt i ⟨k, h_src⟩) (bp.handleAt i)
                    (bp.baseAt i)).1)
    (fun k h_k => do
      let ⟨so, h_safe, h_mmap⟩ ← buildSegmentSafe bp i ⟨k, h_k⟩
      -- `h_mmap` is for `⟨k, h_k⟩`; `fun _ => h_mmap` reuses it for
      -- any `⟨k, h_src⟩` by definitional proof-irrelevance of `<`.
      return ⟨so, h_safe, fun _ => h_mmap⟩)
  return ⟨arr, h_size,
    fun k h_k => (h_p k h_k).1,
    fun k h_k h_src => (h_p k h_k).2 h_src⟩

-- ============================================================================
-- buildElfSafe — assemble one elf's `ElfOps` + its `ElfSafe` witness.
-- Within-elf disjointness chains `mmap_eq` (segment k's built mmap
-- matches setupSlots's output) with `setupSlots_mmap_eq` (closed form
-- of (addr, len)) into `within_elf_mmapRange_disjoint`'s conclusion.
-- ============================================================================

/-- Per-elf invariant carried across `buildLoadElves`: each elf's
    `segments` array has the matching length, and each built segment's
    `mmap` matches what `setupSlots` produced on the source segment.
    The cross-elf disjointness proof in `buildSafe` rewrites along
    these to land in `cross_elf_mmapRange_disjoint`. -/
private def ElfBuildInvariant (bp : BasedPlan) (i : Fin bp.n)
    (eo : ElfOps bp.n) : Prop :=
  eo.segments.size = (bp.elfAt i).segments.size ∧
  (∀ k (h_k : k < eo.segments.size)
    (h_src : k < (bp.elfAt i).segments.size),
    (eo.segments[k]'h_k).mmap =
      (setupSlots (bp.segAt i ⟨k, h_src⟩) (bp.handleAt i) (bp.baseAt i)).1)

/-- Build one `ElfOps` + its `ElfSafe` witness + `ElfBuildInvariant`. -/
def buildElfSafe (bp : BasedPlan) (i : Fin bp.n) :
    Except String { eo : ElfOps bp.n //
      ElfSafe bp.rsv.addr bp.rsv.len eo ∧
      ElfBuildInvariant bp i eo } := do
  let ⟨segments, h_size, h_safe, h_mmap⟩ ← buildElfSegments bp i
  let eo : ElfOps bp.n := { base := bp.baseAt i, segments }
  let h_elfSafe : ElfSafe bp.rsv.addr bp.rsv.len eo := by
    refine ⟨?_, ?_⟩
    · intro k h_k; exact h_safe k h_k
    · -- Within-elf mmap disjointness: for j₁ < j₂, both segments' mmaps
      -- come from setupSlots on the corresponding source segments.
      intro j₁ j₂ h_j₁ h_j₂ h_lt m₁ m₂ h_m₁ h_m₂
      have h_j₁_src : j₁ < (bp.elfAt i).segments.size := by
        rw [h_size] at h_j₁; exact h_j₁
      have h_j₂_src : j₂ < (bp.elfAt i).segments.size := by
        rw [h_size] at h_j₂; exact h_j₂
      have h_mmap_eq₁ := h_mmap j₁ h_j₁ h_j₁_src
      have h_mmap_eq₂ := h_mmap j₂ h_j₂ h_j₂_src
      have h_su₁ : (setupSlots (bp.segAt i ⟨j₁, h_j₁_src⟩) (bp.handleAt i)
            (bp.baseAt i)).1 = some m₁ := by
        rw [← h_mmap_eq₁]; exact h_m₁
      have h_su₂ : (setupSlots (bp.segAt i ⟨j₂, h_j₂_src⟩) (bp.handleAt i)
            (bp.baseAt i)).1 = some m₂ := by
        rw [← h_mmap_eq₂]; exact h_m₂
      have ⟨h_a₁, h_l₁⟩ := setupSlots_mmap_eq (bp.segAt i ⟨j₁, h_j₁_src⟩)
        (bp.handleAt i) (bp.baseAt i) m₁ h_su₁
      have ⟨h_a₂, h_l₂⟩ := setupSlots_mmap_eq (bp.segAt i ⟨j₂, h_j₂_src⟩)
        (bp.handleAt i) (bp.baseAt i) m₂ h_su₂
      have h_disj := bp.within_elf_mmapRange_disjoint i
        ⟨j₁, h_j₁_src⟩ ⟨j₂, h_j₂_src⟩ h_lt
      rw [h_a₁, h_l₁, h_a₂, h_l₂]; exact h_disj
  let h_inv : ElfBuildInvariant bp i eo := ⟨h_size, h_mmap⟩
  return ⟨eo, h_elfSafe, h_inv⟩

-- ============================================================================
-- buildLoadElves — build the array of ElfOps with per-elf
-- `ElfSafe` and `ElfBuildInvariant` invariants. Thin wrapper over
-- `buildSafeArray`.
-- ============================================================================

/-- Build all elves with `ElfSafe` + `ElfBuildInvariant` witnesses. -/
def buildLoadElves (bp : BasedPlan) :
    Except String { result : Array (ElfOps bp.n) //
      result.size = bp.n ∧
      (∀ k (h_k : k < result.size),
        ElfSafe bp.rsv.addr bp.rsv.len (result[k]'h_k)) ∧
      (∀ k (h_k : k < result.size) (h_src : k < bp.n),
        ElfBuildInvariant bp ⟨k, h_src⟩ (result[k]'h_k)) } := do
  -- Combined predicate: ElfSafe ∧ (bound-discharged) ElfBuildInvariant.
  let ⟨arr, h_size, h_p⟩ ← buildSafeArray bp.n
    (fun k eo =>
      ElfSafe bp.rsv.addr bp.rsv.len eo ∧
      ∀ (h_src : k < bp.n), ElfBuildInvariant bp ⟨k, h_src⟩ eo)
    (fun k h_k => do
      let ⟨eo, h_safe, h_inv⟩ ← buildElfSafe bp ⟨k, h_k⟩
      return ⟨eo, h_safe, fun _ => h_inv⟩)
  return ⟨arr, h_size,
    fun k h_k => (h_p k h_k).1,
    fun k h_k h_src => (h_p k h_k).2 h_src⟩

-- ============================================================================
-- buildSafe — the final constructive build. Assembles the full
-- safety-witnessed `LoadOps` via `buildLoadElves` + `LoadSafe` proof.
-- Cross-elf disjointness chains:
--   ElfBuildInvariant.mmap (each elf's segments[k].mmap = setupSlots …)
--   → setupSlots_mmap_eq (closed-form addr/len)
--   → BasedPlan.cross_elf_mmapRange_disjoint
-- The only `Except` failure path is `bakeReloc`'s 32-bit overflow.
-- ============================================================================

/-- Build the `LoadOps` tree + `Safe` witness directly. -/
def buildSafe (bp : BasedPlan) :
    Except String { lo : LoadOps bp.n // Safe bp.rsv.addr bp.rsv.len lo } := do
  let ⟨elves, h_size, h_safe, h_inv⟩ ← buildLoadElves bp
  let lo : LoadOps bp.n := elves
  let h_loadSafe : LoadSafe bp.rsv.addr bp.rsv.len lo := by
    refine ⟨?_, ?_⟩
    · intro k h_k; exact h_safe k h_k
    · -- Cross-elf mmap disjointness.
      intro i₁ i₂ h_i₁ h_i₂ h_lt k_i₁ k_i₂ h_k_i₁ h_k_i₂ m₁ m₂ h_m₁ h_m₂
      have h_i₁_n : i₁ < bp.n := by rw [h_size] at h_i₁; exact h_i₁
      have h_i₂_n : i₂ < bp.n := by rw [h_size] at h_i₂; exact h_i₂
      let fi₁ : Fin bp.n := ⟨i₁, h_i₁_n⟩
      let fi₂ : Fin bp.n := ⟨i₂, h_i₂_n⟩
      have h_inv₁ := h_inv i₁ h_i₁ h_i₁_n
      have h_inv₂ := h_inv i₂ h_i₂ h_i₂_n
      obtain ⟨h_size_eq₁, h_mmap_eq₁⟩ := h_inv₁
      obtain ⟨h_size_eq₂, h_mmap_eq₂⟩ := h_inv₂
      have h_k_src₁ : k_i₁ < (bp.elfAt fi₁).segments.size := by
        rw [h_size_eq₁] at h_k_i₁; exact h_k_i₁
      have h_k_src₂ : k_i₂ < (bp.elfAt fi₂).segments.size := by
        rw [h_size_eq₂] at h_k_i₂; exact h_k_i₂
      have h_mmap_su₁ : (setupSlots (bp.segAt fi₁ ⟨k_i₁, h_k_src₁⟩)
            (bp.handleAt fi₁) (bp.baseAt fi₁)).1 = some m₁ := by
        rw [← h_mmap_eq₁ k_i₁ h_k_i₁ h_k_src₁]; exact h_m₁
      have h_mmap_su₂ : (setupSlots (bp.segAt fi₂ ⟨k_i₂, h_k_src₂⟩)
            (bp.handleAt fi₂) (bp.baseAt fi₂)).1 = some m₂ := by
        rw [← h_mmap_eq₂ k_i₂ h_k_i₂ h_k_src₂]; exact h_m₂
      have ⟨h_a₁, h_l₁⟩ := setupSlots_mmap_eq (bp.segAt fi₁ ⟨k_i₁, h_k_src₁⟩)
        (bp.handleAt fi₁) (bp.baseAt fi₁) m₁ h_mmap_su₁
      have ⟨h_a₂, h_l₂⟩ := setupSlots_mmap_eq (bp.segAt fi₂ ⟨k_i₂, h_k_src₂⟩)
        (bp.handleAt fi₂) (bp.baseAt fi₂) m₂ h_mmap_su₂
      have h_disj := bp.cross_elf_mmapRange_disjoint fi₁ fi₂
        ⟨k_i₁, h_k_src₁⟩ ⟨k_i₂, h_k_src₂⟩ h_lt
      rw [h_a₁, h_l₁, h_a₂, h_l₂]; exact h_disj
  return ⟨lo, safe_of_LoadSafe _ _ lo h_loadSafe⟩

/-- Witnessed build — fully constructive. Assembles the `LoadOps`
    tree alongside its `Safe` witness via `buildSafe`. The only
    `Except` failure path is `bakeReloc`'s 32-bit overflow check
    (psABI per-relocation `OVERFLOW_CHECK`); safety itself is
    established structurally, no decidable fallback.

    Callers consume the result via `LoadOps.runSafe`. -/
def build (bp : BasedPlan) :
    Except String { lo : LoadOps bp.n // Safe bp.rsv.addr bp.rsv.len lo } :=
  buildSafe bp

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

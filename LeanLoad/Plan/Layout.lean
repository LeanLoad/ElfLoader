/-
Layout planning — base-free.

Each PT_LOAD `Segment` is lifted into a `SegmentLayout n` by
`Plan.SegmentLayout` (page math + per-segment invariants + relocs).
This file assembles those into per-elf and global structures:

  • `ElfLayout n` — one elf's `SegmentLayout`s, its `advance` (per-elf
    cursor), plus `segmentsSorted` (page-aligned ranges don't
    overlap) and `pageEndAddr_le_advance` (each segment fits in
    `advance`).
  • `Layout n` — every elf's `ElfLayout` plus the cumulative
    `totalSpan` and the `totalSpan_eq` Nat↔UInt64 bridge.

The natural number parameter `n` is the elf count: every
`Entry` indexes the global elf array with `Fin n`.

`Layout.ofElfs` builds the whole tree in one pass: it consumes
`(elfs, resolveTable)` and produces a fully-planned
`Layout elfs.size`. Per-elf page-aligned non-overlap is validated
as part of construction — failure is rare (modern toolchains never
emit overlapping page ranges) but possible in principle.

Once a `Layout` exists, `assignBases base lp` is total: it stacks
each elf by `alignUp objectSpan 0x1000` from the IO-supplied base.
The closed-form bound `assignBases_at_toNat` feeds
`Materialize.BoundPlan.bases_at_toNat`.

Spec: gabi 07 § Program Header (page-aligned mmap views, base
assignment, span over loadable segments).
-/

import LeanLoad.Plan.SegmentLayout

namespace LeanLoad.Plan

open LeanLoad
open LeanLoad.Parse
open LeanLoad.Elaborate (Elf Segment)
open LeanLoad.Plan.Reloc (Entry)


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
def Sorted (segs : Array (SegmentLayout n)) : Prop :=
  ∀ i, ∀ _ : i < segs.size, ∀ j, ∀ _ : j < segs.size,
    i < j → segs[i].pageEndAddr ≤ segs[j].pageVaddr

instance (segs : Array (SegmentLayout n)) : Decidable (Sorted segs) := by
  unfold Sorted; infer_instance

-- ============================================================================
-- ElfLayout n — one elf's SegmentLayouts + advance + cross-segment bounds.
-- Per-segment bounds (pageEnd_lt, fileOverlay_le_pageLength, …) live
-- on each `SegmentLayout`; `ElfLayout` only carries the genuinely
-- cross-segment / per-elf properties.
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
structure ElfLayout (objCount : Nat) where
  elf            : Elf
  /-- Parallel to `elf.segments`, lifted to the loader view + relocs. -/
  segments       : Array (SegmentLayout objCount)
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

namespace ElfLayout

/-- Build an `ElfLayout n`, validating page-aligned non-overlap.
    `Elaborate.Sorted` and `Elaborate.NonOverlap` are on raw vaddrs;
    after page-rounding, small-alignment edge cases can collapse two
    segments onto the same page (modern toolchains never emit this,
    but it's not statically excluded by gabi-level invariants).

    Reloc planning happens here too: each segment's `relocs` field is
    filled by `Reloc.planSegment`. -/
def ofElf (elfs : Array Elf) (rt : Resolve.Table elfs.size)
    (objectIdx : Fin elfs.size) : Except String (ElfLayout elfs.size) :=
  let e := elfs[objectIdx]
  let segs : Array (SegmentLayout elfs.size) :=
    e.segments.map fun s =>
      SegmentLayout.ofSegmentCore elfs.size s
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
      have h_eq : segs[i]'h_lt = SegmentLayout.ofSegmentCore elfs.size
          (e.segments[i]'h_lt_e)
          (Reloc.planSegment elfs rt objectIdx (e.segments[i]'h_lt_e)) := by
        show (e.segments.map _)[i]'h_lt = _
        rw [Array.getElem_map]
      rw [h_eq]
      -- pageEndAddr.toNat ≤ vaddr + memsz + ea, and that's < 2^48.
      have h_addr := (e.segments[i]'h_lt_e).addrBound
      have h_ea := SegmentLayout.effectiveAlign_le_succ
        (e.segments[i]'h_lt_e).align
      have h_2_48 : (2:Nat)^48 < 2^64 := by decide
      -- pageEndAddr = pageVaddr + pageLength = alignUp (vaddr + memsz) ea (toNat).
      show ((SegmentLayout.ofSegmentCore _ _ _).pageVaddr +
            (SegmentLayout.ofSegmentCore _ _ _).pageLength).toNat ≤ _
      have h_pl := (SegmentLayout.ofSegmentCore elfs.size
        (e.segments[i]'h_lt_e)
        (Reloc.planSegment elfs rt objectIdx
          (e.segments[i]'h_lt_e))).pageEnd_lt
      have h_vm_le := (SegmentLayout.ofSegmentCore elfs.size
        (e.segments[i]'h_lt_e)
        (Reloc.planSegment elfs rt objectIdx
          (e.segments[i]'h_lt_e))).vaddr_memsz_le_pageEnd
      simp only [SegmentLayout.ofSegmentCore_segment] at h_vm_le
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt h_pl]
      -- now goal: pageVaddr.toNat + pageLength.toNat ≤ 2^48
      -- We know vaddr + memsz ≤ pageVaddr + pageLength.
      -- And pageVaddr ≤ vaddr (alignDown). So pageLength = pageEnd - pageVaddr,
      -- pageEnd = alignUp (vaddr + memsz) ea ≤ vaddr + memsz + ea < 2^48.
      simp only [SegmentLayout.ofSegmentCore_pageVaddr,
                 SegmentLayout.ofSegmentCore_pageLength]
      rw [SegmentLayout.pageLength_toNat]
      have h_au_le := SegmentLayout.alignUp_vm_le (e.segments[i]'h_lt_e)
      have h_ad_le : (alignDown (e.segments[i]'h_lt_e).vaddr
                       (effectiveAlign (e.segments[i]'h_lt_e).align)).toNat ≤
                     (e.segments[i]'h_lt_e).vaddr.toNat :=
        UInt64.le_iff_toNat_le.mp (alignDown_le _ _)
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
    .error "ElfLayout.ofElf: PT_LOAD page-aligned ranges overlap"

end ElfLayout

-- ============================================================================
-- Cumulative offset (free function over `Array (ElfLayout n)`) — sum of
-- `advance.toNat` for `k < n`, in `Nat` to dodge UInt64 wrap. The
-- canonical Nat-side anchor for every safety bound.
-- ============================================================================

/-- Sum of `(elfs[k].advance).toNat` for `k < n`, in `Nat`. -/
def cumOffset (elfs : Array (ElfLayout m)) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    if h : n < elfs.size then
      cumOffset elfs n + (elfs[n].advance).toNat
    else
      cumOffset elfs n

@[simp] theorem cumOffset_zero (elfs : Array (ElfLayout m)) :
    cumOffset elfs 0 = 0 := rfl

theorem cumOffset_succ_of_lt (elfs : Array (ElfLayout m)) {n : Nat}
    (h : n < elfs.size) :
    cumOffset elfs (n + 1) = cumOffset elfs n + (elfs[n].advance).toNat := by
  show (if h : n < elfs.size then _ + _ else _) = _
  rw [dif_pos h]

theorem cumOffset_mono (elfs : Array (ElfLayout m)) {a b : Nat} (h : a ≤ b) :
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
-- Layout n — every elf's plan + the cumulative reservation span.
-- The `totalSpan_eq` field connects the UInt64 `totalSpan` to the
-- Nat `cumOffset full` so safety proofs can chain via `Nat`
-- arithmetic. The `elfs_size` field ties the elf array length to `n`
-- so consumers can index totally with `Fin n`.
-- ============================================================================

/-- Top-level base-free plan. `totalSpan` is the `len` to pass to
    `Reserve.run` at the IO boundary; `totalSpan_eq` says it equals
    the `cumOffset` Nat sum (no UInt64 wrap during construction).
    `elfs` is a length-indexed `Vector` so `lp.elfs[i]` is total for
    any `i : Fin objCount` — no separate `elfs_size` rewrite needed
    at indexing sites. -/
structure Layout (objCount : Nat) where
  elfs      : Vector (ElfLayout objCount) objCount
  /-- `Σ alignUp objectSpan 0x1000` — cumulative reservation span. -/
  totalSpan : UInt64
  /-- Connects UInt64 `totalSpan` to the `Nat` cumulative sum.
      Discharged in `ofElfs` by checking the sum fits in UInt64. -/
  totalSpan_eq : totalSpan.toNat = cumOffset elfs.toArray elfs.toArray.size

namespace Layout

/-- Convenience: `lp.cumOffset k` over the elf array. -/
def cumOffset (lp : Layout objCount) (k : Nat) : Nat :=
  _root_.LeanLoad.Plan.cumOffset lp.elfs.toArray k

/-- Tail-recursive accumulator that lifts each `Elf` through
    `ElfLayout.ofElf` while maintaining `acc.size = i`. -/
private def buildElfLayouts (elfs : Array Elf) (rt : Resolve.Table elfs.size)
    (i : Nat) (h : i ≤ elfs.size)
    (acc : { a : Array (ElfLayout elfs.size) // a.size = i }) :
    Except String { a : Array (ElfLayout elfs.size) // a.size = elfs.size } :=
  if heq : i = elfs.size then
    .ok ⟨acc.val, heq ▸ acc.property⟩
  else
    have hi : i < elfs.size := Nat.lt_of_le_of_ne h heq
    match ElfLayout.ofElf elfs rt ⟨i, hi⟩ with
    | .error e => .error e
    | .ok ep =>
      let acc' : { a : Array (ElfLayout elfs.size) // a.size = i + 1 } :=
        ⟨acc.val.push ep, by rw [Array.size_push, acc.property]⟩
      buildElfLayouts elfs rt (i + 1) hi acc'
termination_by elfs.size - i

/-- Build the full base-free plan from raw elfs + resolve table. Each
    elf goes through `ElfLayout.ofElf`, which validates page-aligned
    non-overlap and plans each segment's relocations. Computes the
    `Nat` cumulative span and checks it fits in UInt64 so the
    resulting `Layout` carries the `totalSpan_eq` invariant. -/
private def ofElfsImpl (elfs : Array Elf) (rt : Resolve.Table elfs.size) :
    Except String (Layout elfs.size) := do
  let elfLayouts ← buildElfLayouts elfs rt 0 (Nat.zero_le _) ⟨#[], by simp⟩
  let totalNat :=
    _root_.LeanLoad.Plan.cumOffset elfLayouts.val elfLayouts.val.size
  if h : totalNat < 2 ^ 64 then
    let elfsV : Vector (ElfLayout elfs.size) elfs.size :=
      ⟨elfLayouts.val, elfLayouts.property⟩
    return {
      elfs := elfsV,
      totalSpan := UInt64.ofNat totalNat,
      totalSpan_eq := by
        show totalNat % 2 ^ 64 = _
        have h_to : elfsV.toArray = elfLayouts.val := rfl
        rw [h_to]
        exact Nat.mod_eq_of_lt h }
  else
    .error s!"Layout.ofElfs: cumulative span {totalNat} exceeds UInt64"

/-- Public entry point. The implicit `objCount` defaults to `elfs.size`
    via the `h_size := by rfl` argument (last so callers can omit it);
    pass an explicit `h_size` to retype at any provably-equal size
    (used by `Plan.Aggregate.ofGraph` to land at `Layout
    g.objects.size` without an outer `▸` cast). The `subst h_size;
    exact ofElfsImpl …` body absorbs the rewrite at the wrapper. -/
def ofElfs {objCount : Nat} (elfs : Array Elf) (rt : Resolve.Table objCount)
    (h_size : elfs.size = objCount := by rfl) :
    Except String (Layout objCount) := by
  subst h_size; exact ofElfsImpl elfs rt

end Layout

-- ============================================================================
-- Base assignment via `Array.ofFn` + `cumOffset`. Per-index lemma
-- (`assignBases_at_toNat`) is a one-liner over the closed-form
-- definition.
-- ============================================================================

/-- Stack each elf at `base + cumOffset i`. Total: every `Layout`
    produces a valid bases vector of length `objCount`. -/
def assignBases (base : UInt64) (lp : Layout objCount) : Vector UInt64 objCount :=
  Vector.ofFn fun (i : Fin objCount) =>
    base + UInt64.ofNat (cumOffset lp.elfs.toArray i.val)

/-- The `i`-th base equals `rsvAddr + cumOffset i` in `Nat`, given
    the global no-wrap precondition `rsvAddr.toNat + lp.totalSpan.toNat
    < 2^64` (which `Reserve.noWrap` discharges). Falls out of
    `Vector.getElem_ofFn` plus a small ofNat reduction. -/
theorem assignBases_at_toNat (base : UInt64) (lp : Layout objCount)
    (h_no_wrap : base.toNat + lp.totalSpan.toNat < 2 ^ 64)
    (i : Fin objCount) :
    ((assignBases base lp)[i]).toNat =
    base.toNat + cumOffset lp.elfs.toArray i.val := by
  unfold assignBases
  have h_get : (Vector.ofFn fun (i : Fin objCount) =>
      base + UInt64.ofNat (cumOffset lp.elfs.toArray i.val))[i] =
      base + UInt64.ofNat (cumOffset lp.elfs.toArray i.val) := by simp
  rw [h_get]
  have h_size_eq : lp.elfs.toArray.size = objCount := lp.elfs.size_toArray
  have h_lt_arr : i.val < lp.elfs.toArray.size := h_size_eq.symm ▸ i.isLt
  have h_cum_le : cumOffset lp.elfs.toArray i.val ≤
      cumOffset lp.elfs.toArray lp.elfs.toArray.size :=
    cumOffset_mono _ (Nat.le_of_lt h_lt_arr)
  have h_total_eq : lp.totalSpan.toNat = cumOffset lp.elfs.toArray lp.elfs.toArray.size :=
    lp.totalSpan_eq
  have h_cum_lt : cumOffset lp.elfs.toArray i.val < 2 ^ 64 := by omega
  have h_sum_lt : base.toNat + cumOffset lp.elfs.toArray i.val < 2 ^ 64 := by omega
  rw [UInt64.toNat_add]
  show (base.toNat + (cumOffset lp.elfs.toArray i.val) % 2 ^ 64) % 2 ^ 64 =
       base.toNat + cumOffset lp.elfs.toArray i.val
  rw [Nat.mod_eq_of_lt h_cum_lt, Nat.mod_eq_of_lt h_sum_lt]

end LeanLoad.Plan

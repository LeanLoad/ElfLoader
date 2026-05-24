/-
Per-ELF layout planning -- base-free.

An `ElfLayout n` lifts one parsed ELF into segment layouts plus the
cross-segment invariants needed by finalize:

  * `segmentsSorted`: page-aligned segment ranges do not overlap.
  * `pageEndAddr_le_advance`: every segment fits inside the per-object
    reservation advance.

The natural number parameter `n` is the global object count threaded into
per-segment relocation entries.

Spec: gabi 07 § Program Header (page-aligned mmap views, base assignment, span
over loadable segments).
-/

import LeanLoad.Layout.Segment

namespace LeanLoad.Layout

open LeanLoad
open LeanLoad.Parse
open LeanLoad.Reloc (Entry)

-- ============================================================================
-- UInt64 max helpers -- small lemmas the per-ELF `pageEndAddr_le_advance`
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
    is ≤ the next one's `pageEaddr`. Base-free; translation
    invariant. Same shape as `Parse.Sorted`, but on the
    page-aligned ranges. -/
def Sorted {segCount : Nat} (segs : Vector (SegmentLayout n) segCount) : Prop :=
  ∀ i j : Fin segCount, i < j → (segs[i]).pageEndAddr ≤ (segs[j]).pageEaddr

instance {segCount : Nat} (segs : Vector (SegmentLayout n) segCount) :
    Decidable (Sorted segs) := by
  unfold Sorted; infer_instance

-- ============================================================================
-- ElfLayout n -- one elf's SegmentLayouts + advance + cross-segment bounds.
-- Per-segment bounds (pageEnd_lt, fileOverlay_le_pageLength, ...) live
-- on each `SegmentLayout`; `ElfLayout` only carries the genuinely
-- cross-segment / per-elf properties.
-- ============================================================================

/-- One elf's segment plans, the per-elf cursor advance (page-aligned
    cumulative span), and proofs that
      * the page-aligned ranges don't overlap (`segmentsSorted`),
      * each segment's `pageEndAddr` fits inside `advance`
        (`pageEndAddr_le_advance`) -- the per-elf containment bound
        the safety predicates consume.
    Construction (`ofElf`) is fallible: it fails when the page-
    aligned non-overlap validation rejects the elf, or if the
    `advance` computation would wrap UInt64 (impossible on Linux). -/
structure ElfLayout (objCount : Nat) where
  elf            : Elf
  /-- Indexed by `elf.segments.items`, lifted to the loader view + relocs. -/
  segments       : Vector (SegmentLayout objCount) elf.segments.items.size
  /-- Per-elf cursor advance: at least `alignUp (max pageEndAddr) 0x1000`,
      possibly more if the no-wrap dance demands. The reservation
      reserves exactly `advance` bytes per elf via `assignBases`. -/
  advance        : UInt64
  /-- Pointwise address-range equality for the parallel segment arrays.
      The underlying `Segment` types are heterogeneous because `SegmentLayout`
      existentializes file size; consumers only need the file-size-independent
      runtime address range. -/
  segmentsSegmentRangeEq : ∀ idx : Fin elf.segments.items.size,
    (segments[idx]).segment.eaddr = (elf.segments.items[idx]).eaddr ∧
      (segments[idx]).segment.memsz = (elf.segments.items[idx]).memsz
  /-- Page-aligned segment ranges don't overlap pairwise. -/
  segmentsSorted : Sorted segments
  /-- Each segment's mmap'd range fits in `[0, advance)` (in `Nat`).
      The crux of the per-elf containment bound. -/
  pageEndAddr_le_advance : ∀ idx : Fin elf.segments.items.size,
    (segments[idx]).pageEndAddr.toNat ≤ advance.toNat

namespace ElfLayout

/-- Number of checked PT_LOAD segments. -/
abbrev segmentCount (ep : ElfLayout objCount) : Nat :=
  ep.elf.segments.items.size

/-- Build an `ElfLayout n`, validating page-aligned non-overlap.
    `Parse.Sorted` and `Parse.NonOverlap` are on raw vaddrs;
    after page-rounding, small-alignment edge cases can collapse two
    segments onto the same page (modern toolchains never emit this,
    but it's not statically excluded by gabi-level invariants).

    Callers supply the already-planned relocations for each checked segment. -/
def ofElfCore (objCount : Nat) (e : Elf)
    (segmentRelocs :
      (idx : Fin e.segments.items.size) → Array (Entry objCount e.segments.items[idx])) :
    Except String (ElfLayout objCount) :=
  let segArray : Array (SegmentLayout objCount) :=
    Array.ofFn fun idx : Fin e.segments.items.size =>
      let s := e.segments.items[idx]
      SegmentLayout.ofSegmentCore objCount s (segmentRelocs idx)
  have h_size_eq : segArray.size = e.segments.items.size := by simp [segArray]
  let segs : Vector (SegmentLayout objCount) e.segments.items.size :=
    ⟨segArray, h_size_eq⟩
  if h_sorted : Sorted segs then
    let objectSpan : UInt64 := segArray.foldl (init := 0) fun acc sp =>
      max acc sp.pageEndAddr
    let advance := alignUp objectSpan 0x1000
    if h_no_wrap : objectSpan.toNat + (0x1000 : UInt64).toNat < 2 ^ 64 then
      have h_align_ne : (0x1000 : UInt64) ≠ 0 := by decide
      have h_obj_le_adv : objectSpan ≤ advance :=
        alignUp_ge _ _ h_align_ne h_no_wrap
      have h_obj_le_adv_n := UInt64.le_iff_toNat_le.mp h_obj_le_adv
      have h_pe_le_obj : ∀ idx : Fin e.segments.items.size,
          (segs[idx]).pageEndAddr.toNat ≤ objectSpan.toNat := by
        intro idx
        let motive : Nat → UInt64 → Prop := fun n acc =>
          ∀ (k : Nat) (_ : k < n) (h_size : k < segArray.size),
            segArray[k].pageEndAddr.toNat ≤ acc.toNat
        have h_full : motive segArray.size objectSpan := by
          show motive segArray.size _
          refine Array.foldl_induction motive ?_ ?_
          · intro k h_k _; omega
          · intro idx acc ih k h_k h_size
            show segArray[k].pageEndAddr.toNat ≤
                 (max acc segArray[idx.val].pageEndAddr).toNat
            rw [UInt64.toNat_max]
            rcases Nat.lt_or_ge k idx.val with h_k_lt | h_k_ge
            · have h := ih k h_k_lt h_size
              exact Nat.le_trans h (Nat.le_max_left _ _)
            · have h_eq : k = idx.val := by omega
              subst h_eq
              show segArray[idx.val].pageEndAddr.toNat ≤
                   max acc.toNat segArray[idx.val].pageEndAddr.toNat
              exact Nat.le_max_right _ _
        have h_idx_arr : idx.val < segArray.size := h_size_eq.symm ▸ idx.isLt
        have h := h_full idx.val h_idx_arr h_idx_arr
        simpa [segs] using h
      have h_bound : ∀ idx : Fin e.segments.items.size,
                     (segs[idx]).pageEndAddr.toNat ≤ advance.toNat := by
        intro idx
        have h := h_pe_le_obj idx
        omega
      have h_seg_range_eq : ∀ idx : Fin e.segments.items.size,
          (segs[idx]).segment.eaddr = (e.segments.items[idx]).eaddr ∧
            (segs[idx]).segment.memsz = (e.segments.items[idx]).memsz := by
        intro idx
        have h_get : segs[idx] = SegmentLayout.ofSegmentCore objCount
            (e.segments.items[idx]) (segmentRelocs idx) := by
          simp [segs, segArray]
        rw [h_get]
        exact ⟨rfl, rfl⟩
      .ok { elf := e, segments := segs, advance,
            segmentsSegmentRangeEq := h_seg_range_eq,
            segmentsSorted := h_sorted,
            pageEndAddr_le_advance := h_bound }
    else
      .error s!"plan: object span 0x{objectSpan.toNat} cannot be aligned \
        to 0x1000 without UInt64 wrap"
  else
    .error "ElfLayout.ofElf: PT_LOAD page-aligned ranges overlap"

end ElfLayout

/-- Build an `ElfLayout` from a relocation plan for one object. -/
def ElfLayout.ofElf (rp : Reloc.Result) (objectIdx : Fin rp.objCount) :
    Except String (ElfLayout rp.objCount) :=
  let e := rp.graph.objects[objectIdx].elf
  ElfLayout.ofElfCore rp.objCount e (rp.entries objectIdx)

end LeanLoad.Layout

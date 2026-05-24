/-
Public base-free layout stage.

This module assembles per-ELF `ElfLayout`s into the global `Layout n`:

  * `cumOffset` is the Nat-side cumulative offset anchor used by safety proofs.
  * `Layout n` stores every object's `ElfLayout` plus the total reservation span.
  * `Layout.ofRelocResult` builds the full pure layout from a relocation plan.
  * `assignBases` stacks each object inside the IO-supplied reservation.

The natural number parameter `n` is the object count: every downstream index into
the global object array is a `Fin n`.

Spec: gabi 07 § Program Header (page-aligned mmap views, base assignment, span
over loadable segments).
-/

import LeanLoad.Layout.Elf

namespace LeanLoad.Layout

open LeanLoad
open LeanLoad.Parse

-- ============================================================================
-- Cumulative offset (free function over `Array (ElfLayout n)`) -- sum of
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
-- Layout n -- every elf's plan + the cumulative reservation span.
-- The `totalSpan_eq` field connects the UInt64 `totalSpan` to the
-- Nat `cumOffset full` so safety proofs can chain via `Nat`
-- arithmetic.
-- ============================================================================

/-- Top-level base-free plan. `totalSpan` is the `len` to pass to
    `Runtime.Memory.reserve` at the IO boundary; `totalSpan_eq` says it equals
    the `cumOffset` Nat sum (no UInt64 wrap during construction).
    `elfs` is a length-indexed `Vector` so `lp.elfs[i]` is total for
    any `i : Fin objCount` -- no separate `elfs_size` rewrite needed
    at indexing sites. -/
structure Layout (objCount : Nat) where
  elfs      : Vector (ElfLayout objCount) objCount
  /-- `Σ alignUp objectSpan 0x1000` -- cumulative reservation span. -/
  totalSpan : UInt64
  /-- Connects UInt64 `totalSpan` to the `Nat` cumulative sum.
      Discharged in `ofElfs` by checking the sum fits in UInt64. -/
  totalSpan_eq : totalSpan.toNat = cumOffset elfs.toArray elfs.toArray.size

namespace Layout

/-- Convenience: `lp.cumOffset k` over the elf array. -/
def cumOffset (lp : Layout objCount) (k : Nat) : Nat :=
  _root_.LeanLoad.Layout.cumOffset lp.elfs.toArray k

/-- Tail-recursive accumulator that builds `ElfLayout`s while maintaining
    `acc.size = i`. -/
private def buildElfLayoutsFrom (objCount : Nat)
    (build : (idx : Fin objCount) → Except String (ElfLayout objCount))
    (i : Nat) (h : i ≤ objCount)
    (acc : { a : Array (ElfLayout objCount) // a.size = i }) :
    Except String { a : Array (ElfLayout objCount) // a.size = objCount } :=
  if heq : i = objCount then
    .ok ⟨acc.val, heq ▸ acc.property⟩
  else
    have hi : i < objCount := Nat.lt_of_le_of_ne h heq
    match build ⟨i, hi⟩ with
    | .error e => .error e
    | .ok ep =>
      let acc' : { a : Array (ElfLayout objCount) // a.size = i + 1 } :=
        ⟨acc.val.push ep, by rw [Array.size_push, acc.property]⟩
      buildElfLayoutsFrom objCount build (i + 1) hi acc'
termination_by objCount - i

/-- Build a full array of `ElfLayout`s from a per-index builder. -/
private def buildElfLayouts (objCount : Nat)
    (build : (idx : Fin objCount) → Except String (ElfLayout objCount)) :
    Except String { a : Array (ElfLayout objCount) // a.size = objCount } :=
  buildElfLayoutsFrom objCount build 0 (Nat.zero_le _) ⟨#[], by simp⟩

/-- Construct `Layout` once the per-ELF layouts are known. This is shared by the
    production relocation path and layout-only examples. -/
private def ofElfLayouts (label : String)
    (elfLayouts : { a : Array (ElfLayout objCount) // a.size = objCount }) :
    Except String (Layout objCount) := do
  let totalNat :=
    _root_.LeanLoad.Layout.cumOffset elfLayouts.val elfLayouts.val.size
  if h : totalNat < 2 ^ 64 then
    let elfsV : Vector (ElfLayout objCount) objCount :=
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
    .error s!"{label}: cumulative span {totalNat} exceeds UInt64"

/-- Build the full base-free layout from a relocation plan. Each
    elf goes through `ElfLayout.ofElf`, which validates page-aligned
    non-overlap and attaches already-planned relocation entries. Computes
    the `Nat` cumulative span and checks it fits in UInt64 so the resulting
    `Layout` carries the `totalSpan_eq` invariant. -/
def ofRelocResult (rp : Reloc.Result) : Except String (Layout rp.objCount) := do
  let elfLayouts ← buildElfLayouts rp.objCount (fun idx => ElfLayout.ofElf rp idx)
  ofElfLayouts "Layout.ofRelocResult" elfLayouts

/-- Layout-only helper for synthetic examples with no relocations. -/
def ofElfs (elfs : Array Elf) : Except String (Layout elfs.size) := do
  let elfLayouts ← buildElfLayouts elfs.size (fun idx =>
    ElfLayout.ofElfCore elfs.size elfs[idx] (fun _ => #[]))
  ofElfLayouts "Layout.ofElfs" elfLayouts

end Layout

-- ============================================================================
-- Base assignment via `Vector.ofFn` + `cumOffset`. Per-index lemma
-- (`assignBases_at_toNat`) is a one-liner over the closed-form definition.
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

end LeanLoad.Layout

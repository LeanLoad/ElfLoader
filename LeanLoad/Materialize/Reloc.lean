/-
Relocation **baking** — base-aware.

Phase 2 of 2 in the relocation pipeline:

  1. **Plan** (`Plan/Reloc.lean`) — `RawRela → RelocEntry n seg`. Pure,
     base-free; resolves the symbol reference and stores the result on
     each `SegmentPlan.relocs`.
  2. **Bake** (this file) — `RelocEntry n seg + base → Option Store`.
     Looks up the symbol's absolute value `S = base[target] +
     symtab[target].value` (or 0 when `target = noSymbol`/
     `weakUnresolved`), feeds `(S, A, base, place)` into the per-arch
     `Formula`, and emits a 4-or-8-byte `Store` at `base + r_offset`.
     32-bit writes are overflow-checked (psABI per-relocation
     `OVERFLOW_CHECK`); see the banner below.

The split exists because the kernel picks the per-elf base
(`Reserve.run`) between phases 1 and 2; phase 1 is pure and runs ahead
of any IO.

Entry points:
  • `bakeReloc` — one entry → `Option Store` (none for `R_*_NONE`).
  • `bakeSegmentRelocs` — one segment's relas → flat `Array Store`.

Used by `Materialize.buildSegmentSafe` (one call per segment).
-/

import LeanLoad.Plan.Layout
import LeanLoad.Materialize.LoadOps
import LeanLoad.Elaborate.Reloc

namespace LeanLoad.Materialize

open LeanLoad
open LeanLoad.Plan.Reloc (RelocEntry)
open LeanLoad.Elaborate (Elf Segment Formula FormulaInputs FormulaResult PatchSize)

-- ============================================================================
-- 32-bit overflow check.
--
-- Per-arch psABIs (x86-64 § 4.4.1, AArch64 ELF ABI § 5.7.4) require
-- 32-bit relocations to fit in either signed-32 (`[-2^31, 2^31)`) or
-- unsigned-32 (`[0, 2^32)`) — equivalently, the high 32 bits are all
-- zero (small positive) or all one (sign-extended negative).
--
-- gabi (the generic ELF ABI) doesn't specify this; it lives entirely
-- in per-arch tables. Production loaders (glibc ld.so, musl dynlink,
-- bionic) skip the check and trust the static linker to have caught
-- overflows at link time. We check anyway: defense in depth, fails
-- loud instead of producing silent garbage. Cost is one comparison
-- per 32-bit relocation.
-- ============================================================================

/-- A `UInt64` fits losslessly in either signed-32 or unsigned-32:
    its high 32 bits are all zero (small positive) or all one
    (sign-extended negative). Covers every 32-bit relocation kind in
    the per-arch tables. -/
private def fitsLow32 (v : UInt64) : Bool :=
  let high := v >>> 32
  high == 0 || high == 0xFFFFFFFF

-- ============================================================================
-- Symbol-value resolution: `S = base[target] + symtab[target].value`.
-- ============================================================================

/-- Resolve `S` for a `RelocEntry.target`. Unresolved cases
    (`noSymbol`, `weakUnresolved`) and out-of-bounds `symIdx` (caller
    bug) yield `S = 0`; the formula then sees `S = 0`, which is a
    valid input for every reloc type. -/
private def symValueOf (elfs : Array Elf) (bases : Array UInt64)
    (h_bases : bases.size = elfs.size)
    (target : Plan.Reloc.RelocTarget elfs.size) : UInt64 :=
  match target.symRef? with
  | none => 0
  | some ref =>
    let provBase := bases[ref.objectIdx.val]'(by
      rw [h_bases]; exact ref.objectIdx.isLt)
    match elfs[ref.objectIdx].symtab[ref.symIdx]? with
    | none     => 0
    | some sym => provBase + sym.value

-- ============================================================================
-- Bake one RelocEntry into an Option Store.
-- ============================================================================

/-- Bake one entry. Returns `.ok none` for no-op relocations
    (`R_*_NONE` and unsupported types). Errors out on 32-bit
    relocation overflow. The outer `match` is at the top level (no
    `have`/`let` wrappers) so the characterisation lemmas
    `bakeReloc_ok_some` / `bakeReloc_byteLen_le_8` can split on it
    directly. -/
private def bakeReloc (formula : Formula) (elfs : Array Elf)
    (bases : Array UInt64) (h_bases : bases.size = elfs.size)
    (base : UInt64) (seg : Segment) (entry : RelocEntry elfs.size seg) :
    Except String (Option Store) :=
  match formula entry.type
    { symValue := symValueOf elfs bases h_bases entry.target,
      addend := entry.addend, base,
      place := base + entry.r_offset } with
  | none     => .ok none
  | some res =>
    match res.size with
    | .b8 => .ok (some ({ addr := base + entry.r_offset,
                          size := 8, value := res.value } : Store))
    | .b4 =>
      if fitsLow32 res.value then
        .ok (some ({ addr := base + entry.r_offset,
                     size := 4, value := res.value } : Store))
      else
        .error s!"reloc type {entry.type}: 32-bit overflow at \
          place=0x{(base + entry.r_offset).toNat} \
          (value=0x{res.value.toNat} doesn't fit signed-32 or unsigned-32)"

/-- Bake every entry in one segment into a flat `Array Store`.
    Implemented as `Array.foldlM` so the origin lemma
    `bakeSegmentRelocs_mem_origin` can chain through
    `Array.foldlM`'s induction principle. -/
def bakeSegmentRelocs (formula : Formula) (elfs : Array Elf)
    (bases : Array UInt64) (h_bases : bases.size = elfs.size)
    (base : UInt64) (seg : Segment) (relocs : Array (RelocEntry elfs.size seg)) :
    Except String (Array Store) :=
  relocs.foldlM (init := (#[] : Array Store)) fun acc entry => do
    match ← bakeReloc formula elfs bases h_bases base seg entry with
    | none    => pure acc
    | some w  => pure (acc.push w)

-- ============================================================================
-- bakeReloc characterisation.
--
-- When `bakeReloc` returns `.ok (some s)`, the store's address and
-- size are closed forms of `(base, entry)`. Every store has
-- `size ∈ {4, 8}`, so `s.byteLen.toNat ≤ 8` — exactly the bound
-- `BasedPlan.segment_storeRange_in_rsv` consumes. The
-- `coversRela` witness on the entry comes via `entry.covered`.
-- ============================================================================

/-- `bakeReloc` either errors out (32-bit overflow), returns `.ok
    none` (no-op type), or returns `.ok (some s)` with the closed form
    `s.addr = base + entry.r_offset` and `s.size ∈ {4, 8}`. -/
theorem bakeReloc_ok_some (formula : Formula) (elfs : Array Elf)
    (bases : Array UInt64) (h_bases : bases.size = elfs.size)
    (base : UInt64) (seg : Segment) (entry : RelocEntry elfs.size seg)
    (s : Store)
    (h : bakeReloc formula elfs bases h_bases base seg entry = .ok (some s)) :
    s.addr = base + entry.r_offset ∧ (s.size = 4 ∨ s.size = 8) := by
  unfold bakeReloc at h
  split at h
  · cases h    -- formula = none → .ok none, not .ok (some s)
  · split at h
    · -- b8: inject twice (Except.ok then Option.some) to peel off both
      -- constructors and expose the Store-equality.
      injection h with h_some
      injection h_some with h_eq
      refine ⟨?_, Or.inr ?_⟩
      · have := congrArg Store.addr h_eq; simpa using this.symm
      · have := congrArg Store.size h_eq; simpa using this.symm
    · split at h
      · -- b4 fitsLow32: same destructuring chain.
        injection h with h_some
        injection h_some with h_eq
        refine ⟨?_, Or.inl ?_⟩
        · have := congrArg Store.addr h_eq; simpa using this.symm
        · have := congrArg Store.size h_eq; simpa using this.symm
      · cases h    -- overflow: .error, not .ok

/-- `Store.byteLen.toNat ≤ 8` for any store emitted by `bakeReloc`. -/
theorem bakeReloc_byteLen_le_8 (formula : Formula) (elfs : Array Elf)
    (bases : Array UInt64) (h_bases : bases.size = elfs.size)
    (base : UInt64) (seg : Segment) (entry : RelocEntry elfs.size seg)
    (s : Store)
    (h : bakeReloc formula elfs bases h_bases base seg entry = .ok (some s)) :
    s.byteLen.toNat ≤ 8 := by
  obtain ⟨_, h_size⟩ := bakeReloc_ok_some formula elfs bases h_bases base seg entry s h
  unfold Store.byteLen
  rcases h_size with h4 | h8
  · rw [h4]; decide
  · rw [h8]; decide

-- ============================================================================
-- Origin lemma for bakeSegmentRelocs. Every Store in the output came
-- from some RelocEntry in the input via a successful `bakeReloc`.
-- Proved by `List.foldlM` induction on `relocs.toList`.
-- ============================================================================

/-- Helper: if a step function preserves predicate `P` over the
    accumulator, then `List.foldlM` over an `Except` monad preserves
    `P` on success. The step is given as
    `f acc entry = .ok newAcc → (∀ s ∈ acc, P s) → ∀ s ∈ newAcc, P s`. -/
private theorem listFoldlM_except_preserves {α : Type} {β : Type}
    {P : β → Prop} (f : Array β → α → Except String (Array β))
    (h_step : ∀ acc entry newAcc, f acc entry = .ok newAcc →
      (∀ s ∈ acc, P s) → ∀ s ∈ newAcc, P s)
    (init : Array β) (h_init : ∀ s ∈ init, P s)
    (xs : List α) (out : Array β)
    (h_out : xs.foldlM (m := Except String) f init = .ok out) :
    ∀ s ∈ out, P s := by
  induction xs generalizing init with
  | nil =>
    -- `List.foldlM f init [] = pure init`. For Except, `pure init = .ok init`.
    rw [show (List.foldlM (m := Except String) f init [] : Except String (Array β)) =
        Except.ok init from rfl] at h_out
    injection h_out with h_eq
    rw [← h_eq]; exact h_init
  | cons x xs ih =>
    -- `foldlM f init (x :: xs) = f init x >>= fun acc' => foldlM f acc' xs`.
    cases h_first : f init x with
    | error e =>
      rw [show (List.foldlM (m := Except String) f init (x :: xs)
                : Except String (Array β)) =
              (f init x).bind (fun acc' => List.foldlM f acc' xs) from rfl,
          h_first] at h_out
      cases h_out
    | ok acc' =>
      have h_acc'_P : ∀ s ∈ acc', P s := h_step init x acc' h_first h_init
      have h_rest : List.foldlM (m := Except String) f acc' xs = .ok out := by
        rw [show (List.foldlM (m := Except String) f init (x :: xs)
                  : Except String (Array β)) =
                (f init x).bind (fun acc'' => List.foldlM f acc'' xs) from rfl,
            h_first] at h_out
        exact h_out
      exact ih acc' h_acc'_P h_rest

/-- Every store in `bakeSegmentRelocs`'s `.ok` output was produced by
    `bakeReloc` on some entry of the input array, so it satisfies any
    predicate that `bakeReloc`'s `.ok (some _)` results satisfy
    universally (in particular: `byteLen ≤ 8` + `addr = base +
    entry.r_offset` for some `entry`). -/
theorem bakeSegmentRelocs_storesInvariant (formula : Formula) (elfs : Array Elf)
    (bases : Array UInt64) (h_bases : bases.size = elfs.size)
    (base : UInt64) (seg : Segment) (relocs : Array (RelocEntry elfs.size seg))
    (P : Store → Prop)
    (h_baked : ∀ entry, ∀ s, bakeReloc formula elfs bases h_bases base seg entry =
                              .ok (some s) → P s)
    (out : Array Store)
    (h_out : bakeSegmentRelocs formula elfs bases h_bases base seg relocs = .ok out) :
    ∀ s ∈ out, P s := by
  -- Convert the Array.foldlM to List.foldlM via `Array.foldlM_toList`.
  unfold bakeSegmentRelocs at h_out
  rw [← Array.foldlM_toList] at h_out
  refine listFoldlM_except_preserves _ ?_ #[]
    (by intros _ h_mem; exact absurd h_mem (by simp)) relocs.toList out h_out
  -- Step preserves: case-split on `bakeReloc entry`. The step function
  -- in `bakeSegmentRelocs` does `match ← bakeReloc … with | none =>
  -- pure acc | some w => pure (acc.push w)`. The outer `do` desugars to
  -- a `bind`, so `f acc entry = bakeReloc entry >>= …`.
  intro acc entry newAcc h_step h_acc
  cases h_br : bakeReloc formula elfs bases h_bases base seg entry with
  | error e =>
    -- `bakeReloc = .error e` propagates as `.error e`, contradicts `.ok`.
    rw [show ((do
        match ← bakeReloc formula elfs bases h_bases base seg entry with
        | none => pure acc
        | some w => pure (acc.push w))
        : Except String (Array Store)) =
        (bakeReloc formula elfs bases h_bases base seg entry).bind
          (fun r => match r with | none => pure acc | some w => pure (acc.push w))
        from rfl, h_br] at h_step
    simp [Except.bind] at h_step
  | ok r =>
    rw [show ((do
        match ← bakeReloc formula elfs bases h_bases base seg entry with
        | none => pure acc
        | some w => pure (acc.push w))
        : Except String (Array Store)) =
        (bakeReloc formula elfs bases h_bases base seg entry).bind
          (fun r => match r with | none => pure acc | some w => pure (acc.push w))
        from rfl, h_br] at h_step
    simp [Except.bind, pure, Except.pure] at h_step
    cases r with
    | none =>
      simp at h_step
      intro s h_mem_s
      rw [← h_step] at h_mem_s
      exact h_acc s h_mem_s
    | some w =>
      simp at h_step
      intro s h_mem_s
      rw [← h_step] at h_mem_s
      rcases Array.mem_push.mp h_mem_s with h_in_acc | h_eq
      · exact h_acc s h_in_acc
      · rw [h_eq]; exact h_baked entry w h_br

end LeanLoad.Materialize

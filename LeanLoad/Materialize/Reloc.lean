/-
Bake the base-free `RelocEntry`s attached to each `SegmentPlan n`
into typed `Store` ops once a reservation base is known.

For each entry: look up the symbol's absolute value `S = base[target]
+ symtab[target].value` (or 0 when `target = none`), feed
`(S, A, base, place)` into the per-arch `Formula`, and emit a
4- or 8-byte `Store` at `base + r_offset`. 32-bit writes are
overflow-checked (psABI per-relocation `OVERFLOW_CHECK`); see the
banner in this file.

Entry points:
  • `bakeReloc` — one entry → `Option Store` (none for `R_*_NONE`).
  • `bakeSegmentRelocs` — one segment's relas → flat `Array Store`.

Used by `Materialize.build` per segment.
-/

import LeanLoad.Plan.Layout
import LeanLoad.Materialize.LoadOps
import LeanLoad.Elaborate.Reloc

namespace LeanLoad.Materialize

open LeanLoad
open LeanLoad.Reloc (RelocEntry)
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
    (target : Reloc.RelocTarget elfs.size) : UInt64 :=
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

end LeanLoad.Materialize

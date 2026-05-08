/-
Bake base-free `RelocEntry`s into `MemoryOp.write`s once a
reservation base is known.

For each entry: look up the symbol's absolute value `S = base[target]
+ symtab[target].value` (or 0 when `target = none`), feed
`(S, A, base, place)` into the per-arch `Formula`, and emit a
4- or 8-byte write at `base + r_offset`. 32-bit writes are
overflow-checked (psABI per-relocation `OVERFLOW_CHECK`); see the
banner in this file.

Entry points:
  • `bakeReloc` — one entry → `Option MemoryOp` (none for `R_*_NONE`).
  • `bakeSegmentRelocs` — one segment's relas → flat `Array MemoryOp`.

Used by `Materialize.build` per segment.
-/

import LeanLoad.Plan.Reloc
import LeanLoad.Runtime
import LeanLoad.Elaborate.Reloc

namespace LeanLoad.Materialize

open LeanLoad
open LeanLoad.Reloc (RelocEntry SegmentRelocs)
open LeanLoad.Elaborate (Elf Formula FormulaInputs FormulaResult PatchSize)

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

/-- Resolve `S` for a `RelocEntry.target`. `none` (R_*_NONE,
    unresolved weak) yields `S = 0`. Out-of-bounds `symIdx` (caller
    bug) also yields `0`; the formula then sees `S = 0`, which is a
    valid input for every reloc type. -/
private def symValueOf (elfs : Array Elf) (bases : Array UInt64)
    (h_bases : bases.size = elfs.size)
    (target : Option (Resolve.SymRef elfs.size)) : UInt64 :=
  match target with
  | none => 0
  | some ref =>
    let provBase := bases[ref.objectIdx.val]'(by
      rw [h_bases]; exact ref.objectIdx.isLt)
    match elfs[ref.objectIdx].symtab[ref.symIdx]? with
    | none     => 0
    | some sym => provBase + sym.value

-- ============================================================================
-- Bake one RelocEntry into an Option MemoryOp.
-- ============================================================================

/-- Bake one entry. Returns `.ok none` for no-op relocations
    (`R_*_NONE` and unsupported types). Errors out on 32-bit
    relocation overflow. -/
private def bakeReloc (formula : Formula) (elfs : Array Elf)
    (bases : Array UInt64) (h_bases : bases.size = elfs.size)
    (base : UInt64) (entry : RelocEntry elfs.size) :
    Except String (Option MemoryOp) := do
  let symValue := symValueOf elfs bases h_bases entry.target
  let inputs : FormulaInputs :=
    { symValue, addend := entry.addend, base,
      place := base + entry.r_offset }
  match formula entry.type inputs with
  | none     => .ok none
  | some res =>
    let addr := base + entry.r_offset
    match res.size with
    | .b8 => .ok (some (.write addr 8 res.value))
    | .b4 =>
      if fitsLow32 res.value then
        .ok (some (.write addr 4 res.value))
      else
        .error s!"reloc type {entry.type}: 32-bit overflow at \
          place=0x{addr.toNat} (value=0x{res.value.toNat} doesn't fit \
          signed-32 or unsigned-32)"

/-- Bake every entry in one segment into a flat `Array MemoryOp`. -/
def bakeSegmentRelocs (formula : Formula) (elfs : Array Elf)
    (bases : Array UInt64) (h_bases : bases.size = elfs.size)
    (base : UInt64) (sr : SegmentRelocs elfs.size) :
    Except String (Array MemoryOp) := do
  let mut acc : Array MemoryOp := #[]
  for entry in sr do
    match ← bakeReloc formula elfs bases h_bases base entry with
    | none    => pure ()
    | some op => acc := acc.push op
  return acc

end LeanLoad.Materialize

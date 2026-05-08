/-
Relocation planning — pure.

Consumes per-segment relas (already segment-tied at the validation
boundary, see `Elaborate.Segment.{rela, jmprel}`) plus a per-arch
`Formula` and a resolution table (from `Resolve`); emits a list of
`MemoryOp.write` ops (4- or 8-byte writes per the formula's
`PatchSize`) the runtime loader will execute.

The patch's destination address is computed at planning time:
`addr := base + r_offset`. After realize, `[base + pageVaddr,
base + pageVaddr + pageLength)` is mmap'd and writable; by
`coversRela`, `r_offset` lies in `[vaddr, vaddr + memsz)`, so
`addr` lies in the mmap'd range. Lean-side discipline; kernel-side
trust.
-/

import LeanLoad.Plan.Layout
import LeanLoad.Plan.Resolve
import LeanLoad.Elaborate.Reloc
import LeanLoad.Runtime

namespace LeanLoad.Reloc

open LeanLoad
open LeanLoad.Layout
open LeanLoad.Parse (RawRela)
open LeanLoad.Elaborate (Elf PatchSize FormulaInputs FormulaResult Formula)

-- ============================================================================
-- Symbol-value resolution (used to plug `S` into the formula)
-- ============================================================================

/-- Look up the absolute value of a resolved symbol. -/
def absoluteSymbolValue (elfs : Array Elf) (bases : Array UInt64)
    (ref : Resolve.SymRef elfs.size) : Option UInt64 := do
  let provider := elfs[ref.objectIdx]
  let entry ← provider.symtab[ref.symIdx]?
  let base  ← bases[ref.objectIdx.val]?
  return base + entry.value

/-- Find the resolution for `(objectIdx, symIdx)` in a built table. -/
def lookupResolved (elfs : Array Elf) (rt : Resolve.Table elfs.size)
    (bases : Array UInt64) (objectIdx symIdx : Nat) : Option UInt64 := do
  let ref? ← rt.index[(objectIdx, symIdx)]?
  let ref ← ref?
  absoluteSymbolValue elfs bases ref

/-- Resolve the absolute value of a relocation's symbol reference. -/
def resolveSymValue (elfs : Array Elf) (bases : Array UInt64)
    (rt : Resolve.Table elfs.size) (objectIdx symIdx : Nat) : UInt64 :=
  let result : Option UInt64 := do
    let elf   ← elfs[objectIdx]?
    let base  ← bases[objectIdx]?
    let entry ← elf.symtab[symIdx]?
    if !entry.isUndef then
      return base + entry.value
    else
      lookupResolved elfs rt bases objectIdx symIdx
  result.getD 0

-- ============================================================================
-- Per-rela planning — produces a `MemoryOp.write` of 4 or 8 bytes.
--
-- 32-bit writes are bounds-checked: the formula's `UInt64` result
-- must fit in either signed-32 (`[-2^31, 2^31)`) or unsigned-32
-- (`[0, 2^32)`) — equivalently, its high 32 bits are all zero or
-- all one. Out-of-range values would be silently truncated by
-- `memcpy(addr, &value, 4)` and corrupt the loaded image.
--
-- Where it's specified:
--   • x86-64 psABI § 4.4.1 (Relocation Types) — per-relocation
--     "Field" widths (`word32`/`word64`) plus distinct unsigned/
--     signed 32-bit kinds (`R_X86_64_32` vs `R_X86_64_32S`).
--   • AArch64 ELF ABI (ARM IHI 0056) § 5.7.4 — explicit
--     `OVERFLOW_CHECK` clause per relocation entry.
--
-- Where it's NOT specified: gabi (the generic ELF ABI) — gabi only
-- describes relocation processing abstractly; widths and overflow
-- semantics are per-arch psABI.
--
-- Where production loaders run it: typically nowhere. glibc's
-- `ld.so`, musl's `dynlink`, and bionic compute and write without
-- checking. They trust the static linker (`ld`/`lld`) to have
-- caught all overflows at link time. A correctly-built shared
-- library never produces an overflow at dynamic relocation time.
--
-- Why we keep it anyway: defense in depth for a research loader.
-- An unverified static linker is a trust gap; checking at load
-- time fails loud instead of producing silent garbage. Cost is
-- one comparison per 32-bit relocation, paid in `Reloc.plan`.
-- ============================================================================

/-- A `UInt64` fits losslessly in either signed-32 or unsigned-32:
    its high 32 bits are all zero (small positive) or all one
    (sign-extended negative). The looser-of-the-two check covers
    every 32-bit relocation kind in the per-arch tables. -/
private def fitsLow32 (v : UInt64) : Bool :=
  let high := v >>> 32
  high == 0 || high == 0xFFFFFFFF

/-- Plan one rela inside a region. Returns `.ok none` for no-op
    relocations (`R_*_NONE` and unsupported types). Errors out on
    32-bit relocation overflow (psABI overflow-check, see banner
    above). -/
private def planRela (formula : Formula) (region : Region)
    (symValue : UInt64) (r : RawRela) : Except String (Option MemoryOp) := do
  let inputs : FormulaInputs :=
    { symValue, addend := r.r_addend, base := region.base,
      place := region.base + r.r_offset }
  match formula r.type inputs with
  | none     => .ok none
  | some res =>
    let addr := region.base + r.r_offset
    match res.size with
    | .b8 => .ok (some (.write addr 8 res.value))
    | .b4 =>
      if fitsLow32 res.value then
        .ok (some (.write addr 4 res.value))
      else
        .error s!"reloc type {r.type}: 32-bit overflow at place=0x{(region.base + r.r_offset).toNat} \
          (value=0x{res.value.toNat} doesn't fit signed-32 or unsigned-32)"

/-- Plan all relocations for one elf. -/
def planObject (formula : Formula) (elfs : Array Elf) (bases : Array UInt64)
    (hBases : bases.size = elfs.size)
    (rt : Resolve.Table elfs.size) (objectIdx : Fin elfs.size) :
    Except String (Array MemoryOp) := do
  let elf  := elfs[objectIdx]
  let base := bases[objectIdx.val]'(by rw [hBases]; exact objectIdx.isLt)
  let mut acc : Array MemoryOp := #[]
  for h : segI in [:elf.segments.size] do
    let segIdx : Fin elf.segments.size := ⟨segI, h.upper⟩
    let seg := elf.segments[segIdx]
    let region : Region := { base, seg }
    for entry in seg.rela do
      let r := entry.val
      let symValue : UInt64 :=
        if r.sym == 0 then 0
        else resolveSymValue elfs bases rt objectIdx.val r.sym.toNat
      match ← planRela formula region symValue r with
      | none    => pure ()
      | some op => acc := acc.push op
    for entry in seg.jmprel do
      let r := entry.val
      let symValue : UInt64 :=
        if r.sym == 0 then 0
        else resolveSymValue elfs bases rt objectIdx.val r.sym.toNat
      match ← planRela formula region symValue r with
      | none    => pure ()
      | some op => acc := acc.push op
  return acc

/-- Plan relocations for every elf. -/
def plan (formula : Formula) (elfs : Array Elf)
    (bases : Array UInt64) (hBases : bases.size = elfs.size)
    (rt : Resolve.Table elfs.size) : Except String (Array MemoryOp) := do
  let mut acc : Array MemoryOp := #[]
  for h : i in [:elfs.size] do
    acc := acc ++ (← planObject formula elfs bases hBases rt ⟨i, h.upper⟩)
  return acc

end LeanLoad.Reloc

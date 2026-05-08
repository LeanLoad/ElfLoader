/-
Relocation planning — pure.

Consumes per-segment relas (already segment-tied at the validation
boundary, see `Elaborate.Segment.{rela, jmprel}`) plus a per-arch
`Formula` and a resolution table (from `Resolve`); emits a list of
`MemoryOp.patch64` / `patch32` ops the runtime loader will execute.

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
-- Per-rela planning — produces a `MemoryOp.patch{64,32}`.
-- ============================================================================

/-- Plan one rela inside a region. Returns `none` for no-op
    relocations (`R_*_NONE` and unsupported types). -/
private def planRela (formula : Formula) (region : Region)
    (symValue : UInt64) (r : RawRela) : Option MemoryOp :=
  let inputs : FormulaInputs :=
    { symValue, addend := r.r_addend, base := region.base,
      place := region.base + r.r_offset }
  match formula r.type inputs with
  | none     => none
  | some res =>
    let addr := region.base + r.r_offset
    match res.size with
    | .b8 => some (.patch64 addr res.value)
    | .b4 => some (.patch32 addr res.value)

/-- Plan all relocations for one elf. -/
def planObject (formula : Formula) (elfs : Array Elf) (bases : Array UInt64)
    (hBases : bases.size = elfs.size)
    (rt : Resolve.Table elfs.size) (objectIdx : Fin elfs.size) :
    Array MemoryOp := Id.run do
  let elf  := elfs[objectIdx]
  let base := bases[objectIdx.val]'(by rw [hBases]; exact objectIdx.isLt)
  let mut acc : Array MemoryOp := #[]
  for h : segI in [:elf.segments.size] do
    let segIdx : Fin elf.segments.size := ⟨segI, h.upper⟩
    let seg := elf.segments[segIdx]
    let region : Region := { base, seg }
    let planEntry (acc : Array MemoryOp)
        (entry : { r : Parse.RawRela //
          Elaborate.coversRela seg.vaddr seg.memsz r.r_offset }) :
        Array MemoryOp :=
      let r := entry.val
      let symValue : UInt64 :=
        if r.sym == 0 then 0
        else resolveSymValue elfs bases rt objectIdx.val r.sym.toNat
      match planRela formula region symValue r with
      | none   => acc
      | some op => acc.push op
    acc := seg.rela.foldl planEntry acc
    acc := seg.jmprel.foldl planEntry acc
  return acc

/-- Plan relocations for every elf. -/
def plan (formula : Formula) (elfs : Array Elf)
    (layouts : { a : Array Layout.ObjectLayout // a.size = elfs.size })
    (rt : Resolve.Table elfs.size) : Array MemoryOp := Id.run do
  let bases : Array UInt64 := layouts.val.map (·.base)
  have hBases : bases.size = elfs.size := by simp [bases, layouts.property]
  let mut acc : Array MemoryOp := #[]
  for h : i in [:elfs.size] do
    acc := acc ++ planObject formula elfs bases hBases rt ⟨i, h.upper⟩
  return acc

end LeanLoad.Reloc

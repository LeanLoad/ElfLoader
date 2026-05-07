/-
Relocation planning — pure.

Consumes per-segment relas (already segment-tied at the validation
boundary, see `Elaborate.Segment.{rela, jmprel}`) plus a per-arch
`Formula` and a resolution table (from `Resolve`); emits the list of
`Patch`es the runtime loader will perform.

The formula notation `S, A, B, P` follows gabi 06 and the per-arch
supplements. Per-arch formula tables live under `Spec/Reloc/`.

Each `Patch` is keyed by `(objectIdx, segIdx, offset)` — the
segment-tying inherited from `Elaborate.Segment` means the bounds
check at apply time is structural (the offset is by construction
inside the segment's mmap'd region), not a separate runtime probe.
-/

import LeanLoad.Plan.Discover
import LeanLoad.Plan.Layout
import LeanLoad.Elaborate.Reloc
import LeanLoad.Plan.Resolve

namespace LeanLoad.Reloc

open LeanLoad
open LeanLoad.Discover
open LeanLoad.Layout
open LeanLoad.Parse (RawRela)
open LeanLoad.Elaborate (PatchSize FormulaInputs FormulaResult Formula)

-- ============================================================================
-- A single planned write
-- ============================================================================

/-- One memory write, keyed by `(objectIdx, segIdx)` so the runtime
    knows exactly which mmap'd region to write into. The offset is
    segment-relative (in UInt64, ready for `Region.patchN`). -/
structure Patch (g : ObjectList) where
  /-- Index into `g.val`. -/
  objectIdx : Fin g.val.size
  /-- Index into `g.val[objectIdx].elf.segments`. -/
  segIdx    : Fin g.val[objectIdx].elf.segments.size
  /-- Offset from the segment's mmap'd region base, in bytes. -/
  offset    : UInt64
  /-- Value to write. -/
  value     : UInt64
  /-- Width of the write (4 or 8 bytes). -/
  size      : PatchSize

-- ============================================================================
-- Symbol-value resolution (used to plug `S` into the formula)
-- ============================================================================

/-- Look up the absolute value of a resolved symbol. The `Fin n` in
    `ref.objectIdx` makes the `g.val[…]` indexing total. -/
def absoluteSymbolValue (g : ObjectList) (bases : Array UInt64)
    (ref : Resolve.SymRef g.val.size) : Option UInt64 := do
  let provider := g.val[ref.objectIdx]
  let entry ← provider.elf.symtab[ref.symIdx]?
  let base  ← bases[ref.objectIdx.val]?
  return base + entry.value

/-- Find the resolution for `(objectIdx, symIdx)` in a built table. -/
def lookupResolved (g : ObjectList) (rt : Resolve.Table g.val.size)
    (bases : Array UInt64) (objectIdx symIdx : Nat) : Option UInt64 := do
  let (_, ref?) ← rt.resolved.find? fun (u, _) =>
    u.objectIdx.val == objectIdx && u.symIdx == symIdx
  let ref ← ref?
  absoluteSymbolValue g bases ref

/-- Resolve the absolute value of a relocation's symbol reference.

    Three cases (in priority order):
    1. No `obj`/`base`/`sym` at the given indices: value is 0.
    2. The symbol is *defined* in `obj` itself (`st_shndx ≠ SHN_UNDEF`).
       Use `base + sym.st_value`.
    3. The symbol is undefined in `obj`. Look up the resolution table. -/
def resolveSymValue (g : ObjectList) (bases : Array UInt64)
    (rt : Resolve.Table g.val.size) (objectIdx symIdx : Nat) : UInt64 :=
  let result : Option UInt64 := do
    let obj   ← g.val[objectIdx]?
    let base  ← bases[objectIdx]?
    let entry ← obj.elf.symtab[symIdx]?
    if !entry.isUndef then
      return base + entry.value
    else
      lookupResolved g rt bases objectIdx symIdx
  result.getD 0

-- ============================================================================
-- Per-object planning
-- ============================================================================

/-- Plan one rela inside a specific segment. Returns `none` for no-op
    relocations (`R_*_NONE` and unsupported types). -/
private def planRela (formula : Formula) (g : ObjectList)
    (objectIdx : Fin g.val.size) (segIdx : Fin g.val[objectIdx].elf.segments.size)
    (base : UInt64) (symValue : UInt64) (r : RawRela) : Option (Patch g) :=
  let inputs : FormulaInputs :=
    { symValue, addend := r.r_addend, base, place := base + r.r_offset }
  match formula r.type inputs with
  | none     => none
  | some res =>
    let seg := g.val[objectIdx].elf.segments[segIdx]
    -- Segment-relative offset from the mmap'd region base. The mmap'd
    -- region starts at `seg.pageVaddr` (page-aligned `alignDown` of
    -- the raw `vaddr`); the rela's `r_offset` lies inside the raw
    -- `[vaddr, vaddr + memsz)` range by validation's witness, hence
    -- inside the larger page-aligned region.
    let offset : UInt64 := r.r_offset - seg.pageVaddr
    some { objectIdx, segIdx, offset, value := res.value, size := res.size }

/-- Plan all relocations for one object's segments. -/
def planObject (formula : Formula) (g : ObjectList) (bases : Array UInt64)
    (rt : Resolve.Table g.val.size) (objectIdx : Fin g.val.size) : Array (Patch g) := Id.run do
  let obj  := g.val[objectIdx]
  let base := (bases[objectIdx.val]?).getD 0
  let mut acc : Array (Patch g) := #[]
  for h : segI in [:obj.elf.segments.size] do
    let segIdx : Fin obj.elf.segments.size := ⟨segI, h.upper⟩
    let seg := obj.elf.segments[segIdx]
    let planEntry (acc : Array (Patch g))
        (entry : { r : Parse.RawRela // Elaborate.coversRela seg.vaddr seg.memsz r }) :
        Array (Patch g) :=
      let r := entry.val
      let symValue : UInt64 :=
        if r.sym == 0 then 0
        else resolveSymValue g bases rt objectIdx.val r.sym.toNat
      match planRela formula g objectIdx segIdx base symValue r with
      | none   => acc
      | some p => acc.push p
    acc := seg.rela.foldl planEntry acc
    acc := seg.jmprel.foldl planEntry acc
  return acc

/-- Plan relocations for every object. Pure (no `Except`): every
    rela has been segment-tied at validation, so there's no
    out-of-range failure mode left for the planner to surface. -/
def plan (formula : Formula) (g : ObjectList) (layouts : Array ObjectLayout)
    (rt : Resolve.Table g.val.size) : Array (Patch g) := Id.run do
  let bases : Array UInt64 := layouts.map (·.base)
  let mut acc : Array (Patch g) := #[]
  for h : i in [:g.val.size] do
    acc := acc ++ planObject formula g bases rt ⟨i, h.upper⟩
  return acc

end LeanLoad.Reloc

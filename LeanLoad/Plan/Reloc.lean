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
    segment-relative (in UInt64, ready for `Region.patchN`). The
    `coversRela` witness on the originating rela is carried so
    `Exec.applyPatch` can discharge `Region.InRange` structurally
    (via `Layout.patch_inRange`) instead of re-checking at runtime. -/
structure Patch (g : ObjectList) where
  /-- Index into `g.val`. -/
  objectIdx : Fin g.val.size
  /-- Index into `g.val[objectIdx].elf.segments`. -/
  segIdx    : Fin g.val[objectIdx].elf.segments.size
  /-- Originating rela. Kept (instead of just `r.r_offset`) so the
      `coversRela` witness has a `RawRela` to refer to. -/
  rela      : Parse.RawRela
  /-- Witness from validation: the rela's 8-byte write window lies
      inside the segment's `[vaddr, vaddr + memsz)` range. -/
  covers    : Elaborate.coversRela
                g.val[objectIdx].elf.segments[segIdx].vaddr
                g.val[objectIdx].elf.segments[segIdx].memsz
                rela
  /-- Value to write. -/
  value     : UInt64
  /-- Width of the write (4 or 8 bytes). -/
  size      : PatchSize

namespace Patch

/-- Segment-relative offset (from the page-aligned mmap base). -/
def offset {g : ObjectList} (p : Patch g) : UInt64 :=
  p.rela.r_offset - g.val[p.objectIdx].elf.segments[p.segIdx].pageVaddr

end Patch

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

/-- Find the resolution for `(objectIdx, symIdx)` in a built table.
    O(1) via `Resolve.Table.index` (a HashMap built in lock-step with
    `resolved`). -/
def lookupResolved (g : ObjectList) (rt : Resolve.Table g.val.size)
    (bases : Array UInt64) (objectIdx symIdx : Nat) : Option UInt64 := do
  let ref? ← rt.index[(objectIdx, symIdx)]?
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
    relocations (`R_*_NONE` and unsupported types). The `coversRela`
    witness on the input rela carries through to the `Patch.covers`
    field, where `Exec.applyPatch` consumes it via `Layout.patch_inRange`. -/
private def planRela (formula : Formula) (g : ObjectList)
    (objectIdx : Fin g.val.size) (segIdx : Fin g.val[objectIdx].elf.segments.size)
    (base : UInt64) (symValue : UInt64)
    (entry : { r : RawRela //
      Elaborate.coversRela
        g.val[objectIdx].elf.segments[segIdx].vaddr
        g.val[objectIdx].elf.segments[segIdx].memsz r }) :
    Option (Patch g) :=
  let r := entry.val
  let inputs : FormulaInputs :=
    { symValue, addend := r.r_addend, base, place := base + r.r_offset }
  match formula r.type inputs with
  | none     => none
  | some res =>
    some { objectIdx, segIdx, rela := r, covers := entry.property,
           value := res.value, size := res.size }

/-- Plan all relocations for one object's segments. The `bases` array
    is sized to `g.val.size` so per-object indexing is total. -/
def planObject (formula : Formula) (g : ObjectList) (bases : Array UInt64)
    (hBases : bases.size = g.val.size)
    (rt : Resolve.Table g.val.size) (objectIdx : Fin g.val.size) : Array (Patch g) := Id.run do
  let obj  := g.val[objectIdx]
  let base := bases[objectIdx.val]'(by rw [hBases]; exact objectIdx.isLt)
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
      match planRela formula g objectIdx segIdx base symValue entry with
      | none   => acc
      | some p => acc.push p
    acc := seg.rela.foldl planEntry acc
    acc := seg.jmprel.foldl planEntry acc
  return acc

/-- Plan relocations for every object. Pure (no `Except`): every
    rela has been segment-tied at validation, so there's no
    out-of-range failure mode left for the planner to surface. The
    sized-`layouts` subtype gives a `bases.size = g.val.size` proof
    that flows into `planObject`. -/
def plan (formula : Formula) (g : ObjectList)
    (layouts : { a : Array ObjectLayout // a.size = g.val.size })
    (rt : Resolve.Table g.val.size) : Array (Patch g) := Id.run do
  let bases : Array UInt64 := layouts.val.map (·.base)
  have hBases : bases.size = g.val.size := by simp [bases, layouts.property]
  let mut acc : Array (Patch g) := #[]
  for h : i in [:g.val.size] do
    acc := acc ++ planObject formula g bases hBases rt ⟨i, h.upper⟩
  return acc

end LeanLoad.Reloc

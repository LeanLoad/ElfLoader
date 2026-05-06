/-
Relocation planning — pure.

Consumes parsed `Rela` entries (from `Spec.Reloc`) plus a per-arch
`Formula` and a resolution table (from `Resolve`); emits the
list of `Patch`s the runtime loader will perform.

The formula notation `S, A, B, P` follows gabi 06 and the per-arch
supplements. Per-arch formula tables live under `Spec/Reloc/`.
-/

import LeanLoad.DiscoverPlan
import LeanLoad.Layout
import LeanLoad.Spec.Reloc
import LeanLoad.Spec.Symbol
import LeanLoad.Resolve

namespace LeanLoad.Reloc

open LeanLoad
open LeanLoad.Discover
open LeanLoad.Layout

-- ============================================================================
-- A single planned write
-- ============================================================================

/-- One memory write computed from a relocation entry, parameterised by
    the dep graph's object count `n`. The `objectIdx : Fin n` carries
    the bounds proof at the type level — `Apply.applyPatch` indexes
    into `image.objects` totally, no `?`/`throw` needed. -/
structure Patch (n : Nat) where
  /-- Index into `DepGraph.objects` of the object whose memory is
      being written to (the relocation's "P" object). -/
  objectIdx : Fin n
  /-- Target virtual address (post base relocation). -/
  targetVa  : UInt64
  /-- Value to write. -/
  value     : UInt64
  /-- Width of the write in bytes (typically 4 or 8). -/
  size      : Nat
  deriving Repr

/-- Inputs to a single relocation formula. Notation follows gabi 06. -/
structure FormulaInputs where
  /-- `S` — value of the resolved symbol (post base relocation). -/
  symValue : UInt64
  /-- `A` — addend (from `r_addend` for `Rela`). -/
  addend   : UInt64
  /-- `B` — base of the object containing the relocation site. -/
  base     : UInt64
  /-- `P` — virtual address being relocated. -/
  place    : UInt64
  deriving Repr

/-- The result of applying a relocation formula. -/
structure FormulaResult where
  value : UInt64
  size  : Nat
  deriving Repr, BEq

/-- A relocation formula: an interpretation of `(type, inputs)`. -/
abbrev Formula := UInt32 → FormulaInputs → Option FormulaResult

-- ============================================================================
-- Per-object planning
-- ============================================================================

/-- Look up the absolute value of a resolved symbol. -/
def absoluteSymbolValue (g : DepGraph) (bases : Array UInt64)
    (ref : Resolve.SymRef) : Option UInt64 := do
  let provider ← g.objects[ref.objectIdx]?
  let sym ← provider.elf.symtab[ref.symIdx]?
  let base ← bases[ref.objectIdx]?
  return base + sym.st_value

/-- Find the resolution for `(objectIdx, symIdx)` in a built table. -/
def lookupResolved (rt : Resolve.Table) (g : DepGraph)
    (bases : Array UInt64) (objectIdx symIdx : Nat) : Option UInt64 := do
  let (_, ref?) ← rt.resolved.find? fun (u, _) =>
    u.objectIdx == objectIdx && u.symIdx == symIdx
  let ref ← ref?
  absoluteSymbolValue g bases ref

/-- Resolve the absolute value of a relocation's symbol reference.

    Three cases (in priority order):
    1. No `obj`/`base`/`sym` at the given indices: value is 0.
    2. The symbol is *defined* in `obj` itself (`st_shndx ≠ SHN_UNDEF`).
       Use `base + sym.st_value`.
    3. The symbol is undefined in `obj`. Look up the resolution table. -/
def resolveSymValue (g : DepGraph) (bases : Array UInt64)
    (rt : Resolve.Table) (objectIdx symIdx : Nat) : UInt64 :=
  let result : Option UInt64 := do
    let obj  ← g.objects[objectIdx]?
    let base ← bases[objectIdx]?
    let sym  ← obj.elf.symtab[symIdx]?
    if sym.st_shndx != Spec.Symbol.SHN_UNDEF then
      return base + sym.st_value
    else
      lookupResolved rt g bases objectIdx symIdx
  result.getD 0

/-- A write fits its object's mmap'd region: the byte range
    `[targetVa, targetVa + size)` lies in `[base, base + span)`. -/
def Patch.inRange (w : Patch n) (base span : UInt64) : Bool :=
  decide (base ≤ w.targetVa ∧ (w.targetVa - base).toNat + w.size ≤ span.toNat)

/-- Apply `formula` to a single rela: compute inputs, run the formula,
    bounds-check the result. Returns `none` for no-op relocations
    (`R_*_NONE` and unsupported types) or a `Patch` ready to apply.
    Per-rela building block for `planObject`; also the simplest entry
    point for testing per-arch formulas. -/
def planRela {n : Nat} (formula : Formula) (base span : UInt64)
    (objectIdx : Fin n) (symValue : UInt64 := 0) (r : Spec.Reloc.Rela64) :
    Except String (Option (Patch n)) := do
  let inputs : FormulaInputs :=
    { symValue, addend := r.r_addend, base, place := base + r.r_offset }
  match formula r.type inputs with
  | none     => return none
  | some res =>
    let w : Patch n :=
      { objectIdx, targetVa := base + r.r_offset, value := res.value, size := res.size }
    unless w.inRange base span do
      throw s!"reloc out of range: object={objectIdx.val} target={w.targetVa} size={w.size}"
    return some w

/-- Plan all relocations for one object's `.rela.dyn` + `.rela.plt`,
    rejecting any patch whose target falls outside `[base, base + span)`. -/
def planObject (formula : Formula) (g : DepGraph)
    (layouts : Array ObjectLayout) (bases : Array UInt64)
    (rt : Resolve.Table) (objectIdx : Fin g.objects.size) :
    Except String (Array (Patch g.objects.size)) := do
  let obj := g.objects[objectIdx]
  let some lyt := layouts[objectIdx.val]? | return #[]
  let mut acc : Array (Patch g.objects.size) := #[]
  for r in obj.elf.rela ++ obj.elf.jmprel do
    let symValue : UInt64 :=
      if r.sym == 0 then 0
      else resolveSymValue g bases rt objectIdx.val r.sym.toNat
    if let some w ← planRela formula lyt.base lyt.span objectIdx symValue r then
      acc := acc.push w
  return acc

/-- Plan relocations for every object. Fails fast on the first
    out-of-range write — the loader refuses to apply any reloc unless
    every reloc passes the bounds check. -/
def plan (formula : Formula) (g : DepGraph)
    (layouts : Array ObjectLayout) (rt : Resolve.Table) :
    Except String (Array (Patch g.objects.size)) := do
  let bases : Array UInt64 := layouts.map (·.base)
  let mut acc : Array (Patch g.objects.size) := #[]
  for h : i in [:g.objects.size] do
    let chunk ← planObject formula g layouts bases rt ⟨i, h.upper⟩
    acc := acc ++ chunk
  return acc

end LeanLoad.Reloc

/-
Relocation planning — pure.

Consumes parsed `Rela` entries (from `Spec.Reloc`) plus a per-arch
`Formula` and a resolution table (from `Resolve`); emits the
list of `Patch`s the runtime loader will perform.

The formula notation `S, A, B, P` follows gabi 06 and the per-arch
supplements. Per-arch formula tables live under `Spec/Reloc/`.
-/

import LeanLoad.Plan.Discover
import LeanLoad.Plan.Layout
import LeanLoad.Spec.Reloc
import LeanLoad.Spec.Symbol
import LeanLoad.Plan.Resolve

namespace LeanLoad.Reloc

open LeanLoad
open LeanLoad.Discover
open LeanLoad.Layout
open LeanLoad.Spec.Reloc (PatchSize FormulaInputs FormulaResult Formula)

-- The formula-input/output types (`PatchSize`, `FormulaInputs`,
-- `FormulaResult`, `Formula`) live in `Spec.Reloc` so per-arch
-- formula tables can define formulas without depending on the
-- planner; opened above so unqualified names work below.

-- ============================================================================
-- A single planned write
-- ============================================================================

/-- One memory write computed from a relocation entry, parameterised by
    the dep graph's object count `n`. The `objectIdx : Fin n` carries
    the bounds proof at the type level — `Apply.applyPatch` indexes
    into `image.objects` totally, no `?`/`throw` needed. -/
structure Patch (n : Nat) where
  /-- Index into `ObjectList.objects` of the object whose memory is
      being written to (the relocation's "P" object). -/
  objectIdx : Fin n
  /-- Target virtual address (post base relocation). -/
  targetVa  : UInt64
  /-- Value to write. -/
  value     : UInt64
  /-- Width of the write (4 or 8 bytes). -/
  size      : PatchSize
  deriving Repr

-- ============================================================================
-- Per-object planning
-- ============================================================================

/-- Look up the absolute value of a resolved symbol. The `Fin n` in
    `ref.objectIdx` makes the `g.val[…]` indexing total. -/
def absoluteSymbolValue (g : ObjectList) (bases : Array UInt64)
    (ref : Resolve.SymRef g.val.size) : Option UInt64 := do
  let provider := g.val[ref.objectIdx]
  let sym ← provider.elf.symtab[ref.symIdx]?
  let base ← bases[ref.objectIdx.val]?
  return base + sym.st_value

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
    let obj  ← g.val[objectIdx]?
    let base ← bases[objectIdx]?
    let sym  ← obj.elf.symtab[symIdx]?
    if sym.st_shndx != Spec.Symbol.SHN_UNDEF then
      return base + sym.st_value
    else
      lookupResolved g rt bases objectIdx symIdx
  result.getD 0

/-- A write fits its object's mmap'd region: the byte range
    `[targetVa, targetVa + size)` lies in `[base, base + span)`. -/
def Patch.inRange (w : Patch n) (base span : UInt64) : Bool :=
  decide (base ≤ w.targetVa ∧ (w.targetVa - base).toNat + w.size.toNat ≤ span.toNat)

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
      throw s!"reloc out of range: object={objectIdx.val} target={w.targetVa} size={w.size.toNat}"
    return some w

/-- Plan all relocations for one object's `.rela.dyn` + `.rela.plt`,
    rejecting any patch whose target falls outside `[base, base + span)`. -/
def planObject (formula : Formula) (g : ObjectList)
    (layouts : Array ObjectLayout) (bases : Array UInt64)
    (rt : Resolve.Table g.val.size) (objectIdx : Fin g.val.size) :
    Except String (Array (Patch g.val.size)) := do
  let obj := g.val[objectIdx]
  let some lyt := layouts[objectIdx.val]? | return #[]
  let mut acc : Array (Patch g.val.size) := #[]
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
def plan (formula : Formula) (g : ObjectList)
    (layouts : Array ObjectLayout) (rt : Resolve.Table g.val.size) :
    Except String (Array (Patch g.val.size)) := do
  let bases : Array UInt64 := layouts.map (·.base)
  let mut acc : Array (Patch g.val.size) := #[]
  for h : i in [:g.val.size] do
    let chunk ← planObject formula g layouts bases rt ⟨i, h.upper⟩
    acc := acc ++ chunk
  return acc

section Example
open LeanLoad.Spec

-- Toy AArch64 formula table: just the two types this Example
-- exercises (`R_AARCH64_RELATIVE` and `R_AARCH64_NONE`). Real
-- per-arch tables live in `Spec/Reloc/{Aarch64,X86_64}.lean`.
private def toyFormula : Formula := fun ty inp =>
  if ty == 1027 then some { value := inp.base + inp.addend, size := .b8 }
  else if ty == 0 then none
  else none

-- One R_AARCH64_RELATIVE rela: r_info=1027 (sym=0, type=1027),
-- r_addend=0xa90, r_offset=0x1000. With base=0x10000, span=0x100000:
-- targetVa = base + r_offset = 0x11000; value = base + addend = 0x10a90.
private def relativeRela : Reloc.Rela64 :=
  { r_offset := 0x1000, r_info := 1027, r_addend := 0xa90 }

-- A RELATIVE reloc inside the object's span → `some` with the right
-- value/size/offset.
#guard match planRela (n := 1) toyFormula 0x10000 0x100000 ⟨0, by decide⟩
                      (r := relativeRela) with
       | .ok (some p) => p.size.toNat == 8 ∧ p.value == 0x10a90 ∧ p.targetVa == 0x11000
       | _            => false

-- R_AARCH64_NONE → no patch (`some none` after the `Except` layer).
#guard match planRela (n := 1) toyFormula 0x10000 0x100000 ⟨0, by decide⟩
                      (r := { r_offset := 0x1000, r_info := 0, r_addend := 0 }) with
       | .ok none => true
       | _        => false

-- A RELATIVE reloc whose targetVa falls past the span → `Except.error`
-- (bounds check at planning time means Apply never sees an OOB patch).
#guard match planRela (n := 1) toyFormula 0x10000 0x10
                      ⟨0, by decide⟩ (r := relativeRela) with
       | .error _ => true
       | _        => false
end Example

end LeanLoad.Reloc

/-
Relocation planning — pure.

Consumes parsed `Rela` entries (from `Spec.Reloc`) plus a per-arch
`Formula` and a resolution table (from `Plan.Resolve`); emits the
list of `RelocWrite`s the runtime loader will perform.

The formula notation `S, A, B, P` follows gabi 06 and the per-arch
supplements. Per-arch formula tables live under `Spec/Reloc/`.
-/

import LeanLoad.Discover
import LeanLoad.Spec.Reloc
import LeanLoad.Spec.Symbol
import LeanLoad.Plan.Resolve

namespace LeanLoad.Plan.Reloc

open LeanLoad

-- ============================================================================
-- A single planned write
-- ============================================================================

/-- One memory write computed from a relocation entry. -/
structure RelocWrite where
  /-- Index into `LinkMap.objects` of the object whose memory is
      being written to (the relocation's "P" object). -/
  objectIdx : Nat
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

/-- Bases array: chosen load base for each object in `LinkMap.objects`. -/
abbrev Bases := Array UInt64

-- ============================================================================
-- Per-object planning
-- ============================================================================

/-- Look up the absolute value of a resolved symbol. -/
def absoluteSymbolValue (lm : Discover.LinkMap) (bases : Bases)
    (ref : Plan.Resolve.SymRef) : Option UInt64 := do
  let provider ← lm.objects[ref.objectIdx]?
  let sym ← provider.elf.symtab[ref.symIdx]?
  let base ← bases[ref.objectIdx]?
  return base + sym.st_value

/-- Find the resolution for `(objectIdx, symIdx)` in a built table. -/
def lookupResolved (rt : Plan.Resolve.ResolutionTable) (lm : Discover.LinkMap)
    (bases : Bases) (objectIdx symIdx : Nat) : Option UInt64 := do
  let (_, ref?) ← rt.resolved.find? fun (u, _) =>
    u.objectIdx == objectIdx && u.symIdx == symIdx
  let ref ← ref?
  absoluteSymbolValue lm bases ref

/-- Resolve the absolute value of a relocation's symbol reference.

    Three cases (in priority order):
    1. `r.sym == 0`: no symbol; value is 0.
    2. The symbol is *defined* in `obj` itself (`st_shndx ≠ SHN_UNDEF`).
       Use `obj.base + sym.st_value`.
    3. The symbol is undefined in `obj`. Look up the resolution table. -/
def resolveSymValue (lm : Discover.LinkMap) (bases : Bases)
    (rt : Plan.Resolve.ResolutionTable) (obj : Discover.LoadedObject)
    (base : UInt64) (objectIdx : Nat) (symIdx : Nat) : UInt64 :=
  match obj.elf.symtab[symIdx]? with
  | none     => 0
  | some sym =>
    if sym.st_shndx != Spec.Symbol.SHN_UNDEF then
      base + sym.st_value
    else
      (lookupResolved rt lm bases objectIdx symIdx).getD 0

/-- Plan all relocations for one object's `.rela.dyn` + `.rela.plt`. -/
def planObject (formula : Formula) (lm : Discover.LinkMap) (bases : Bases)
    (rt : Plan.Resolve.ResolutionTable) (objectIdx : Nat) : Array RelocWrite := Id.run do
  let some obj := lm.objects[objectIdx]? | return #[]
  let some base := bases[objectIdx]? | return #[]
  let process (entries : Array Spec.Reloc.Rela64) (acc : Array RelocWrite) : Array RelocWrite := Id.run do
    let mut out := acc
    for r in entries do
      let symValue : UInt64 :=
        if r.sym == 0 then 0
        else resolveSymValue lm bases rt obj base objectIdx r.sym.toNat
      let inputs : FormulaInputs :=
        { symValue, addend := r.r_addend, base, place := base + r.r_offset }
      match formula r.type inputs with
      | none => pure ()
      | some res =>
        out := out.push
          { objectIdx, targetVa := base + r.r_offset, value := res.value, size := res.size }
    return out
  let mut writes : Array RelocWrite := #[]
  writes := process obj.elf.rela writes
  writes := process obj.elf.jmprel writes
  return writes

/-- Plan relocations for every object. -/
def plan (formula : Formula) (lm : Discover.LinkMap) (bases : Bases)
    (rt : Plan.Resolve.ResolutionTable) : Array RelocWrite := Id.run do
  let mut all : Array RelocWrite := #[]
  for i in [:lm.objects.size] do
    all := all ++ planObject formula lm bases rt i
  return all

end LeanLoad.Plan.Reloc

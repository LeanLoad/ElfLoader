/-
Relocation planning.

A `RelocWrite` is a single planned modification to a loaded object's
memory: at virtual address `targetVa` of object `objectIdx`, write
`size` bytes containing `value`. `Link.Reloc` is pure — it consumes
parsed `Rela` entries plus the resolution table, and emits the writes
the runtime loader will perform.

Architecture-specific relocation-type formulas live in
`LeanLoad.Link.Reloc.Aarch64` (and, in the future, `.X86_64`). The
selector `formulaFor` returns the right formula based on
`elf.header.e_machine`.

Spec: gabi 06 § Relocation, x86-64-ABI § Relocation Types,
ARM ELF for the AArch64 ABI § Dynamic Relocations.
-/

import LeanLoad.Discover
import LeanLoad.Link.Resolve

namespace LeanLoad.Link.Reloc

open LeanLoad
open LeanLoad.Parse

-- ============================================================================
-- A single planned write
-- ============================================================================

/-- One memory write computed from a relocation entry. -/
structure RelocWrite where
  /-- Index into `Closure.objects` of the object whose memory is
      being written to (the relocation's "P" object). -/
  objectIdx : Nat
  /-- Target virtual address (post base relocation). -/
  targetVa  : UInt64
  /-- Value to write. -/
  value     : UInt64
  /-- Width of the write in bytes (typically 4 or 8). -/
  size      : Nat
  deriving Repr

/-- Inputs to a single relocation formula. Notation follows gabi 06
    and the AArch64 / x86-64 supplements. -/
structure FormulaInputs where
  /-- `S` — value of the resolved symbol (post base relocation). -/
  symValue : UInt64
  /-- `A` — addend (from `r_addend` for `Rela`, implicit for `Rel`). -/
  addend   : UInt64
  /-- `B` — base of the object containing the relocation site. -/
  base     : UInt64
  /-- `P` — virtual address being relocated (the write target). -/
  place    : UInt64
  deriving Repr

/-- The result of applying a relocation formula: a value to write and
    the size, or `none` if the relocation type is unsupported. -/
structure FormulaResult where
  value : UInt64
  size  : Nat
  deriving Repr, BEq

/-- A relocation formula: an interpretation of `(type, inputs)`. -/
abbrev Formula := UInt32 → FormulaInputs → Option FormulaResult

-- ============================================================================
-- Per-object planning
-- ============================================================================

/-- Bases array: the chosen load base for each object in
    `Closure.objects`, indexed by `objectIdx`. -/
abbrev Bases := Array UInt64

/-- Look up the absolute value of a resolved symbol: the symbol's
    `st_value` plus the provider's base address. -/
def absoluteSymbolValue (li : Discover.Closure) (bases : Bases)
    (ref : Resolve.SymRef) : Option UInt64 := do
  let provider ← li.objects[ref.objectIdx]?
  let sym ← provider.elf.symtab[ref.symIdx]?
  let base ← bases[ref.objectIdx]?
  return base + sym.st_value

/-- Find the resolution for `(objectIdx, symIdx)` in a built table.
    Returns the resolved symbol address if any (or `none` if the
    symbol either failed to resolve or is not in the table). -/
def lookupResolved (rt : Resolve.ResolutionTable) (li : Discover.Closure)
    (bases : Bases) (objectIdx symIdx : Nat) : Option UInt64 := do
  let (_, ref?) ← rt.resolved.find? fun (u, _) =>
    u.objectIdx == objectIdx && u.symIdx == symIdx
  let ref ← ref?
  absoluteSymbolValue li bases ref

/-- Plan all relocations for one object's `.rela.dyn` + `.rela.plt`,
    given its base address, the resolution table, and the architecture
    formula. -/
def planObject (formula : Formula) (li : Discover.Closure) (bases : Bases)
    (rt : Resolve.ResolutionTable) (objectIdx : Nat) : Array RelocWrite := Id.run do
  let some obj := li.objects[objectIdx]? | return #[]
  let some base := bases[objectIdx]? | return #[]
  let mut writes : Array RelocWrite := #[]
  let process (entries : Array Reloc.Rela64) (acc : Array RelocWrite) : Array RelocWrite := Id.run do
    let mut out := acc
    for r in entries do
      let symValue : UInt64 :=
        if r.sym == 0 then 0
        else (lookupResolved rt li bases objectIdx r.sym.toNat).getD 0
      let inputs : FormulaInputs :=
        { symValue, addend := r.r_addend, base, place := base + r.r_offset }
      match formula r.type inputs with
      | none => pure ()  -- unsupported / NONE — skip
      | some res =>
        out := out.push
          { objectIdx, targetVa := base + r.r_offset, value := res.value, size := res.size }
    return out
  writes := process obj.elf.rela writes
  writes := process obj.elf.jmprel writes
  return writes

/-- Plan relocations for every object. -/
def plan (formula : Formula) (li : Discover.Closure) (bases : Bases)
    (rt : Resolve.ResolutionTable) : Array RelocWrite := Id.run do
  let mut all : Array RelocWrite := #[]
  for i in [:li.objects.size] do
    all := all ++ planObject formula li bases rt i
  return all

end LeanLoad.Link.Reloc

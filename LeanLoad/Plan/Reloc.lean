/-
Relocation planning.

A `RelocWrite` is a single planned modification to a loaded object's
memory: at virtual address `targetVa` of object `objectIdx`, write
`size` bytes containing `value`. `Plan.Reloc` is pure — it consumes
parsed `Rela` entries plus the resolution table, and emits the writes
the runtime loader will perform.

Architecture-specific relocation-type formulas live in
`LeanLoad.Plan.Reloc.Aarch64` (and, in the future, `.X86_64`). The
selector `formulaFor` returns the right formula based on
`elf.header.e_machine`.

Spec: gabi 06 § Relocation, x86-64-ABI § Relocation Types,
ARM ELF for the AArch64 ABI § Dynamic Relocations.
-/

import LeanLoad.Discover
import LeanLoad.Plan.Resolve

namespace LeanLoad.Plan.Reloc

open LeanLoad
open LeanLoad.Parse

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
    `LinkMap.objects`, indexed by `objectIdx`. -/
abbrev Bases := Array UInt64

/-- Look up the absolute value of a resolved symbol: the symbol's
    `st_value` plus the provider's base address. -/
def absoluteSymbolValue (lm : Discover.LinkMap) (bases : Bases)
    (ref : Resolve.SymRef) : Option UInt64 := do
  let provider ← lm.objects[ref.objectIdx]?
  let sym ← provider.elf.symtab[ref.symIdx]?
  let base ← bases[ref.objectIdx]?
  return base + sym.st_value

/-- Find the resolution for `(objectIdx, symIdx)` in a built table.
    Returns the resolved symbol address if any (or `none` if the
    symbol either failed to resolve or is not in the table). -/
def lookupResolved (rt : Resolve.ResolutionTable) (lm : Discover.LinkMap)
    (bases : Bases) (objectIdx symIdx : Nat) : Option UInt64 := do
  let (_, ref?) ← rt.resolved.find? fun (u, _) =>
    u.objectIdx == objectIdx && u.symIdx == symIdx
  let ref ← ref?
  absoluteSymbolValue lm bases ref

/-- Resolve the absolute value of a relocation's symbol reference.

    Three cases (in priority order):
    1. `r.sym == 0`: no symbol; value is 0.
    2. The symbol is *defined* in `obj` itself (`st_shndx ≠ SHN_UNDEF`).
       Use `obj.base + sym.st_value`. This is the common case for
       intra-object references like libc's GOT entries to its own
       globals (`__environ`, `__stack_chk_guard`, ...).
    3. The symbol is undefined in `obj`. Look up the resolution
       table built by `Resolve` for a defining object. -/
def resolveSymValue (lm : Discover.LinkMap) (bases : Bases)
    (rt : Resolve.ResolutionTable) (obj : Discover.LoadedObject)
    (base : UInt64) (objectIdx : Nat) (symIdx : Nat) : UInt64 :=
  match obj.elf.symtab[symIdx]? with
  | none     => 0
  | some sym =>
    if sym.st_shndx != Parse.Symbol.SHN_UNDEF then
      base + sym.st_value
    else
      (lookupResolved rt lm bases objectIdx symIdx).getD 0

/-- Plan all relocations for one object's `.rela.dyn` + `.rela.plt`. -/
def planObject (formula : Formula) (lm : Discover.LinkMap) (bases : Bases)
    (rt : Resolve.ResolutionTable) (objectIdx : Nat) : Array RelocWrite := Id.run do
  let some obj := lm.objects[objectIdx]? | return #[]
  let some base := bases[objectIdx]? | return #[]
  let process (entries : Array Reloc.Rela64) (acc : Array RelocWrite) : Array RelocWrite := Id.run do
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
    (rt : Resolve.ResolutionTable) : Array RelocWrite := Id.run do
  let mut all : Array RelocWrite := #[]
  for i in [:lm.objects.size] do
    all := all ++ planObject formula lm bases rt i
  return all

end LeanLoad.Plan.Reloc

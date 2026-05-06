/-
Map: lay out each object's `PT_LOAD` segments in mmap'd memory.

Goes through `LeanLoad.Region` (the trust boundary for memory ops).

- `ET_EXEC` (= 2): each mapping is its own `MAP_FIXED` region at its
  absolute `vaddr`. Base = 0 (vaddrs are already absolute).
- `ET_DYN`/PIE / `ET_REL`: one big anonymous region for the whole
  object, kernel-chosen base. Each mapping gets `mprotectRange` on
  its sub-range.

The IO writes that follow (relocation entries) live in `Apply.lean`.
-/

import LeanLoad.Discover
import LeanLoad.Layout
import LeanLoad.Reloc
import LeanLoad.Region

namespace LeanLoad.Load

open LeanLoad

/-- mmap a planned mapping at its absolute `vaddr`, copy bytes, then
    mprotect. Used for `ET_EXEC` objects. -/
def mapMapping (bytes : ByteArray) (m : Layout.Mapping) : IO Region.Region := do
  let region ← Region.mmapAnonFixed m.vaddr m.length.toUSize
  if m.fileLen > 0 then
    let src := bytes.extract m.fileOff.toNat (m.fileOff.toNat + m.fileLen.toNat)
    Region.write region m.pageInset.toUSize src
  Region.mprotect region m.prot
  return region

/-- The contiguous span an object's mappings need (relative). -/
def objectSpan (lyt : Layout.ObjectLayout) : UInt64 :=
  lyt.mappings.foldl (init := 0) fun m mapping => max m (mapping.vaddr + mapping.length)

/-- Map one object, dispatching by `e_type`. Returns its
    region(s) and the chosen base address. -/
def mapObject (lm : Discover.LinkMap) (lyt : Layout.ObjectLayout)
    : IO (Array Region.Region × UInt64) := do
  let some obj := lm.objects[lyt.objectIdx]?
    | throw (IO.userError s!"mapObject: missing {lyt.objectIdx}")
  let bytes := obj.elf.bytes
  if obj.elf.header.e_type = 2 then
    let mut regions := Array.mkEmpty lyt.mappings.size
    for m in lyt.mappings do
      regions := regions.push (← mapMapping bytes m)
    return (regions, 0)
  let region ← Region.mmapAnon (objectSpan lyt).toUSize
  for m in lyt.mappings do
    if m.fileLen > 0 then
      let src := bytes.extract m.fileOff.toNat (m.fileOff.toNat + m.fileLen.toNat)
      Region.write region (m.vaddr + m.pageInset).toUSize src
  for m in lyt.mappings do
    Region.mprotectRange region m.vaddr.toUSize m.length.toUSize m.prot
  return (#[region], Region.base region)

/-- Map every object in a link map. Returns one region array per
    object plus the chosen base addresses. -/
def mapAll (lm : Discover.LinkMap) (plan : Layout.Layout)
    : IO (Array (Array Region.Region) × Reloc.Bases) := do
  let mut all : Array (Array Region.Region) := Array.mkEmpty plan.layouts.size
  let mut bases : Reloc.Bases := Array.mkEmpty plan.layouts.size
  for lyt in plan.layouts do
    let (regions, base) ← mapObject lm lyt
    all := all.push regions
    bases := bases.push base
  return (all, bases)

end LeanLoad.Load

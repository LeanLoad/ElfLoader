/-
Materialise: turn each `ObjectLayout` into one or more `mmap`'d
regions, copy the file-backed bytes in, and `mprotect` to the
planned permissions.

Spec: gabi 02 § Object File Types (`e_type`), gabi 07 § Base Address.

Strategy depends on the object's `e_type`:
- `ET_EXEC` (= 2, gabi 02): each mapping is its own `MAP_FIXED`
  region at its absolute `vaddr`. Base = 0 (vaddrs are already
  absolute, per gabi 07 § Base Address).
- `ET_DYN`/PIE / `ET_REL`: one big anonymous region for the whole
  object, kernel-chosen base. Each mapping gets `mprotectRange` on
  its sub-range.
-/

import LeanLoad.Discover
import LeanLoad.Plan.Layout
import LeanLoad.Plan.Reloc
import LeanLoad.FFI.Region

namespace LeanLoad.Load

open LeanLoad.FFI

/-- mmap a planned mapping at its absolute `vaddr`, copy bytes, then
    mprotect. Used for `ET_EXEC` objects. -/
def materializeMapping (bytes : ByteArray) (m : Plan.Layout.Mapping) : IO Region.Region := do
  let region ← Region.mmapAnonFixed m.vaddr m.length.toUSize
  if m.fileLen > 0 then
    let src := bytes.extract m.fileOff.toNat (m.fileOff.toNat + m.fileLen.toNat)
    Region.write region m.pageInset.toUSize src
  Region.mprotect region m.prot
  return region

/-- The contiguous span an object's mappings need (relative). -/
def objectSpan (lyt : Plan.Layout.ObjectLayout) : UInt64 := Id.run do
  let mut maxEnd : UInt64 := 0
  for m in lyt.mappings do
    let endAddr := m.vaddr + m.length
    if endAddr > maxEnd then maxEnd := endAddr
  return maxEnd

/-- Materialise one object, dispatching by `e_type`. Returns its
    region(s) and the chosen base address. -/
def materializeObject (lm : Discover.LinkMap) (lyt : Plan.Layout.ObjectLayout)
    : IO (Array Region.Region × UInt64) := do
  let some obj := lm.objects[lyt.objectIdx]?
    | throw (IO.userError s!"materializeObject: missing {lyt.objectIdx}")
  let bytes := obj.elf.bytes
  if obj.elf.header.e_type = 2 then
    let mut regions := Array.mkEmpty lyt.mappings.size
    for m in lyt.mappings do
      regions := regions.push (← materializeMapping bytes m)
    return (regions, 0)
  let region ← Region.mmapAnon (objectSpan lyt).toUSize
  for m in lyt.mappings do
    if m.fileLen > 0 then
      let src := bytes.extract m.fileOff.toNat (m.fileOff.toNat + m.fileLen.toNat)
      Region.write region (m.vaddr + m.pageInset).toUSize src
  for m in lyt.mappings do
    Region.mprotectRange region m.vaddr.toUSize m.length.toUSize m.prot
  return (#[region], Region.base region)

/-- Materialise every object in a link map. Returns one region array per
    object plus the chosen base addresses. -/
def materializeAll (lm : Discover.LinkMap) (plan : Plan.Layout.LoaderPlan)
    : IO (Array (Array Region.Region) × Plan.Reloc.Bases) := do
  let mut all : Array (Array Region.Region) := Array.mkEmpty plan.layouts.size
  let mut bases : Plan.Reloc.Bases := Array.mkEmpty plan.layouts.size
  for lyt in plan.layouts do
    let (regions, base) ← materializeObject lm lyt
    all := all.push regions
    bases := bases.push base
  return (all, bases)

end LeanLoad.Load

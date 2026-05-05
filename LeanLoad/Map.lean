/-
The "memory" half of `Load`: map each `ObjectLayout` into mmap'd
regions, then write the planned `RelocWrite`s into them.

Both stages here go through `LeanLoad.FFI.Region` (the trust boundary
for memory operations).

Map (gabi 02 § `e_type`, gabi 07 § Base Address):
- `ET_EXEC` (= 2): each mapping is its own `MAP_FIXED` region at its
  absolute `vaddr`. Base = 0 (vaddrs are already absolute).
- `ET_DYN`/PIE / `ET_REL`: one big anonymous region for the whole
  object, kernel-chosen base. Each mapping gets `mprotectRange` on
  its sub-range.

Apply (gabi 06 § Relocation): the pure planner (`Plan.Reloc`) decides
*what* to write; this file is the trusted IO that does it. Width
safety (`size ∈ {4, 8}`) is proven by `Thm.formula_size_valid`, so
the `unsupported width` branch is unreachable for plans built from
the AArch64 formula.
-/

import LeanLoad.Discover
import LeanLoad.Plan.Layout
import LeanLoad.Plan.Reloc
import LeanLoad.Region

namespace LeanLoad.Load

open LeanLoad

-- ============================================================================
-- Map (mmap + bytes-copy + mprotect)
-- ============================================================================

/-- mmap a planned mapping at its absolute `vaddr`, copy bytes, then
    mprotect. Used for `ET_EXEC` objects. -/
def mapMapping (bytes : ByteArray) (m : Plan.Layout.Mapping) : IO Region.Region := do
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

/-- Map one object, dispatching by `e_type`. Returns its
    region(s) and the chosen base address. -/
def mapObject (lm : Discover.LinkMap) (lyt : Plan.Layout.ObjectLayout)
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
def mapAll (lm : Discover.LinkMap) (plan : Plan.Layout.LoaderPlan)
    : IO (Array (Array Region.Region) × Plan.Reloc.Bases) := do
  let mut all : Array (Array Region.Region) := Array.mkEmpty plan.layouts.size
  let mut bases : Plan.Reloc.Bases := Array.mkEmpty plan.layouts.size
  for lyt in plan.layouts do
    let (regions, base) ← mapObject lm lyt
    all := all.push regions
    bases := bases.push base
  return (all, bases)

-- ============================================================================
-- Apply relocations
-- ============================================================================

/-- Serialize a `UInt64` as 8 little-endian bytes. -/
private def UInt64.toLEBytes (x : UInt64) : ByteArray :=
  ByteArray.mk #[
    (x &&& 0xff).toUInt8,
    ((x >>>  8) &&& 0xff).toUInt8,
    ((x >>> 16) &&& 0xff).toUInt8,
    ((x >>> 24) &&& 0xff).toUInt8,
    ((x >>> 32) &&& 0xff).toUInt8,
    ((x >>> 40) &&& 0xff).toUInt8,
    ((x >>> 48) &&& 0xff).toUInt8,
    ((x >>> 56) &&& 0xff).toUInt8 ]

/-- Serialize the low 32 bits of a `UInt64` as 4 little-endian bytes. -/
private def UInt64.toLEBytes32 (x : UInt64) : ByteArray :=
  ByteArray.mk #[
    (x &&& 0xff).toUInt8,
    ((x >>>  8) &&& 0xff).toUInt8,
    ((x >>> 16) &&& 0xff).toUInt8,
    ((x >>> 24) &&& 0xff).toUInt8 ]

#guard (UInt64.toLEBytes 0x1122334455667788).toList == [0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11]
#guard (UInt64.toLEBytes32 0x12345678).toList == [0x78, 0x56, 0x34, 0x12]

/-- Apply one `RelocWrite` to the right region within the object.
    For ET_DYN we mmap'd one contiguous region per object, so the
    offset within is `targetVa - base`. ET_EXEC binaries normally
    have no relocations to apply. -/
def applyReloc (allRegions : Array (Array Region.Region))
    (bases : Plan.Reloc.Bases) (w : Plan.Reloc.RelocWrite) : IO Unit := do
  let some regions := allRegions[w.objectIdx]?
    | throw (IO.userError s!"applyReloc: missing object {w.objectIdx}")
  let some base := bases[w.objectIdx]?
    | throw (IO.userError s!"applyReloc: missing base {w.objectIdx}")
  let bytes ←
    if w.size = 8 then pure (UInt64.toLEBytes w.value)
    else if w.size = 4 then pure (UInt64.toLEBytes32 w.value)
    else throw (IO.userError s!"applyReloc: unsupported width {w.size}")
  let some region := regions[0]?
    | throw (IO.userError s!"applyReloc: no regions for object {w.objectIdx}")
  let offset := (w.targetVa - base).toUSize
  Region.write region offset bytes

def applyAllRelocs (allRegions : Array (Array Region.Region))
    (bases : Plan.Reloc.Bases) (writes : Array Plan.Reloc.RelocWrite) : IO Unit := do
  for w in writes do applyReloc allRegions bases w

end LeanLoad.Load

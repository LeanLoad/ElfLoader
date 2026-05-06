/-
Apply: walk the planned `RelocWrite`s and poke bytes into mmap'd
memory. Trusted IO; the *what* is decided by `LeanLoad.Reloc`'s pure
planner. Width safety (`size ∈ {4, 8}`) is proven by
`Thm.formula_size_valid`, so the `unsupported width` branch is
unreachable for plans built from a supported per-arch formula.
-/

import LeanLoad.Discover
import LeanLoad.Reloc
import LeanLoad.Region

namespace LeanLoad.Load

open LeanLoad

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
    (bases : Reloc.Bases) (w : Reloc.RelocWrite) : IO Unit := do
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
    (bases : Reloc.Bases) (writes : Array Reloc.RelocWrite) : IO Unit := do
  for w in writes do applyReloc allRegions bases w

end LeanLoad.Load

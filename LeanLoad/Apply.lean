/-
Apply: walk the planned `Patch`es and poke bytes into mmap'd
memory. Trusted IO; the *what* is decided by `LeanLoad.Reloc`'s pure
planner. Width safety (`size ∈ {4, 8}`) is proven by
`Thm.formula_size_valid`, so the `unsupported width` branch is
unreachable for plans built from a supported per-arch formula.
-/

import LeanLoad.Discover
import LeanLoad.Layout
import LeanLoad.Map
import LeanLoad.Reloc
import LeanLoad.Resolve
import LeanLoad.Runtime

namespace LeanLoad.Apply

open LeanLoad
open LeanLoad.Discover
open LeanLoad.Layout

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

section UnitTest
-- Distinct-byte input: each byte appears exactly where you'd expect.
#guard (UInt64.toLEBytes 0x1122334455667788).toList == [0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11]
#guard (UInt64.toLEBytes32 0x12345678).toList == [0x78, 0x56, 0x34, 0x12]
-- Zero serializes to all zeros at both widths.
#guard (UInt64.toLEBytes 0).toList   == [0, 0, 0, 0, 0, 0, 0, 0]
#guard (UInt64.toLEBytes32 0).toList == [0, 0, 0, 0]
-- All-ones: every byte is 0xff.
#guard (UInt64.toLEBytes 0xFFFFFFFFFFFFFFFF).toList == [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
-- 32-bit serializer truncates the high 32 bits silently.
#guard (UInt64.toLEBytes32 0xCAFEBABE12345678).toList == [0x78, 0x56, 0x34, 0x12]
end UnitTest

/-- Apply one `Patch` by writing into its object's reservation
    `Region` at `offset = p.targetVa - lyt.base`. Bounds were
    verified upstream in `Reloc.plan`. -/
def applyPatch (image : Map.ProcessImage) (p : Reloc.Patch) : IO Unit := do
  let some obj := image.objects[p.objectIdx]?
    | throw (IO.userError s!"applyPatch: missing object {p.objectIdx}")
  let some lyt := image.layouts[p.objectIdx]?
    | throw (IO.userError s!"applyPatch: missing layout {p.objectIdx}")
  let bytes ←
    if p.size = 8 then pure (UInt64.toLEBytes p.value)
    else if p.size = 4 then pure (UInt64.toLEBytes32 p.value)
    else throw (IO.userError s!"applyPatch: unsupported width {p.size}")
  let offset := (p.targetVa - lyt.base).toUSize
  Runtime.write obj.reservation offset bytes

/-- Apply every planned patch. Bounds rejection happens upstream in
    `Reloc.plan`, so by the time patches reach here every target VA
    is guaranteed in `[base, base + span)` for its object. -/
def applyPatches (image : Map.ProcessImage) (patches : Array Reloc.Patch) : IO Unit := do
  for p in patches do applyPatch image p

-- ============================================================================
-- Integration test runner. Pokes the planned patches through. The
-- interesting bug-class (wrong width, target out of range, reading
-- past mmap end) surfaces as IO errors, so completing without
-- raising is the assertion.
-- ============================================================================

/-- Self-contained: re-runs Map and Reloc-plan internally so the
    dispatch table can stay flat (`IO Nat`). Cost: extra mmaps that
    persist for the process lifetime — negligible for our fixtures. -/
def test (g : DepGraph) (layouts : Array ObjectLayout)
    (formula : Reloc.Formula) (rt : Resolve.Table) : IO Nat := do
  let image ← Map.mapAll g layouts
  match Reloc.plan formula g layouts rt with
  | .error e =>
    IO.eprintln s!"Reloc.plan: {e}"
    return 1
  | .ok patches =>
    applyPatches image patches
    return 0

end LeanLoad.Apply

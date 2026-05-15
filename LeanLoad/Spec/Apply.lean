/-
Per-op pure denotation.

Each `Op.apply` is the pure shadow of `Op.run`'s byte-level effect.
Tree-level `apply` (per-segment, per-elf, top-level) mirrors
`LoadOps.runUnsafe` exactly: same ops, same order, same fold shape.

The natural number param `objCount` (the elf count) just threads
through; the denotation doesn't depend on it.

Layered correspondence:

  · `MmapOp.apply`      — overlay file bytes at `[addr, addr+len)`
  · `ZeroOp.apply`      — clear bytes at `[addr, addr+len)`
  · `StoreOp.apply`     — write little-endian bytes at `[addr, addr+byteLen)`
  · `MprotectOp.apply`  — byte-level no-op (only perm changes; perm
                          not modelled)
  · `SegmentOps.apply`  — mmap? → zero? → stores → mprotect
  · `ElfOps.apply`      — fold over segments in declared order
  · `LoadOps.apply`     — fold over elves in declared order

Address-arithmetic convention: each in-range test is in `Nat` via
`.toNat` (avoids UInt64 wrap). When the test holds, the file-offset
or store-byte-index lookup uses ordinary UInt64 arithmetic, safe
because the in-range bound has already ruled out the wrapping case.

Spec layering:

  Phase 1 (this file): pure denotation. No theorems yet — just the
    functions. The three soundness theorems (`bytes_preserved`,
    `bss_zeroed`, `relocs_applied`) consume `LoadOps.apply` and live
    in a follow-up file.

  Phase 2 (`Spec/FFI.lean`): the FFI axiom relates the IO effect of
    `LoadOps.runSafe` to `LoadOps.apply` starting from `Memory.zero`.
-/

import LeanLoad.Spec.Memory
import LeanLoad.Spec.File
import LeanLoad.Materialize.LoadOps

namespace LeanLoad

open LeanLoad.Spec

-- ============================================================================
-- Per-op denotations. Each lifts its slot record to a `Memory → Memory`.
-- ============================================================================

namespace MmapOp

/-- File-overlay denotation. Bytes in `[m.addr, m.addr + m.len)` read
    the corresponding file byte `fs.byte m.handle (m.offset + k)` for
    `k = a - m.addr`. Mirrors Linux `mmap(2)` MAP_PRIVATE | MAP_FIXED
    semantics on a `MAP_ANONYMOUS` reservation: file bytes overlay
    the reserved zero-page tiles within the requested span. -/
def apply (fs : File) (m : MmapOp) (mem : Memory) : Memory :=
  fun a =>
    if m.addr.toNat ≤ a.toNat ∧ a.toNat < m.addr.toNat + m.len.toNat then
      fs.byte m.handle (m.offset + (a - m.addr))
    else
      mem a

end MmapOp

namespace ZeroOp

/-- Zero denotation. Bytes in `[z.addr, z.addr + z.len)` read `0`. Used
    for the partial-page BSS tail where a file overlay carries non-zero
    file bytes that the loaded program must see as zero. -/
def apply (z : ZeroOp) (mem : Memory) : Memory :=
  fun a =>
    if z.addr.toNat ≤ a.toNat ∧ a.toNat < z.addr.toNat + z.len.toNat then
      0
    else
      mem a

end ZeroOp

namespace StoreOp

/-- Little-endian write denotation. Byte `i = a - s.addr` of the
    `[s.addr, s.addr + s.byteLen)` window reads
    `(s.value >>> (8 * i)).toUInt8`. Matches the
    `memcpy(dst, &value, size)` in `runtime/runtime.c` on
    little-endian hardware (every supported arch). -/
def apply (s : StoreOp) (mem : Memory) : Memory :=
  fun a =>
    if s.addr.toNat ≤ a.toNat ∧ a.toNat < s.addr.toNat + s.byteLen.toNat then
      let i := a.toNat - s.addr.toNat
      (s.value >>> UInt64.ofNat (8 * i)).toUInt8
    else
      mem a

end StoreOp

namespace MprotectOp

/-- `mprotect` only adjusts access rights, not byte contents. Since
    `Memory` does not model permissions, the denotation is a byte-level
    identity. If/when a soundness theorem demands perm reasoning, add
    a parallel `perm : UInt64 → Perm` field on `Memory` and a
    matching `applyPerm`. -/
def apply (_ : MprotectOp) (mem : Memory) : Memory := mem

end MprotectOp

-- ============================================================================
-- Tree-level denotations. Each mirrors the corresponding `runUnsafe`
-- branch in `Materialize/Safety.lean` exactly.
-- ============================================================================

namespace Materialize.SegmentOps

open LeanLoad.Spec

/-- Per-segment denotation. Composition order matches
    `SegmentOps.runUnsafe`:
      mmap?  → zero?  → stores (in array order)  → mprotect
    The two `Option` slots default to identity when `none`. -/
def apply (fs : File) (so : SegmentOps n) (mem : Memory) : Memory :=
  let m₁ := match so.mmap with
            | some m => m.apply fs mem
            | none   => mem
  let m₂ := match so.zero with
            | some z => z.apply m₁
            | none   => m₁
  let m₃ := so.stores.foldl (init := m₂) fun m s => s.apply m
  so.mprotect.apply m₃

end Materialize.SegmentOps

namespace Materialize.ElfOps

open LeanLoad.Spec

/-- Per-elf denotation. Folds the segment denotations in declared
    order. -/
def apply (fs : File) (eo : ElfOps n) (mem : Memory) : Memory :=
  eo.segments.foldl (init := mem) fun m so => so.apply fs m

end Materialize.ElfOps

namespace Materialize.LoadOps

open LeanLoad.Spec

/-- Top-level denotation. Folds the per-elf denotations in declared
    order (main at index 0). The result is the abstract memory state
    that `LoadOps.runSafe` is axiomatized to realize (see
    `Spec/FFI.lean`). -/
def apply (fs : File) (lo : LoadOps n) (mem : Memory) : Memory :=
  lo.foldl (init := mem) fun m eo => eo.apply fs m

end Materialize.LoadOps

end LeanLoad

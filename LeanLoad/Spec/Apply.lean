/-
Per-op pure denotation over the byte + perm `Memory` model.

Each `Op.apply` is the pure shadow of `Op.run`'s effect on both
the byte function and the permission function. Tree-level `apply`
(per-segment, per-elf, top-level) mirrors `LoadOps.runUnsafe`
exactly: same ops, same order, same fold shape.

The natural number param `objCount` (the elf count) just threads
through; the denotation doesn't depend on it.

Layered correspondence:

  · `MmapOp.apply`     — overlay file bytes at `[addr, addr+len)`;
                          set perm to `prot | PROT_WRITE` over that
                          range (widened so subsequent stores can land).
  · `ZeroOp.apply`     — clear bytes at `[addr, addr+len)`; perm
                          unchanged (we're still in the pre-mprotect
                          PROT_RW window).
  · `StoreOp.apply`    — write little-endian bytes at
                          `[addr, addr+byteLen)`; perm unchanged.
  · `MprotectOp.apply` — bytes unchanged; set perm to `m.prot` over
                          `[addr, addr+len)`. Final permission for
                          the segment.
  · `SegmentOps.apply` — mmap? → zero? → stores → mprotect.
  · `ElfOps.apply`     — fold over segments in declared order.
  · `LoadOps.apply`    — fold over elves in declared order.

Address-arithmetic convention: each in-range test is in `Nat` via
`.toNat` (avoids UInt64 wrap). When the test holds, the file-offset
or store-byte-index lookup uses ordinary UInt64 arithmetic, safe
because the in-range bound has already ruled out the wrapping case.
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

/-- File-overlay denotation. In `[m.addr, m.addr + m.len)`:
      · `byte` reads the corresponding file byte
        `fs.byte m.handle (m.offset + (a - m.addr))`.
      · `perm` reads `m.prot ||| PROT_WRITE` (widened so subsequent
        relocation stores can run before `mprotect` flips to final
        perm).
    Outside the range, both fields unchanged. -/
def apply (fs : File) (m : MmapOp) (mem : Memory) : Memory where
  byte := fun a =>
    if m.addr.toNat ≤ a.toNat ∧ a.toNat < m.addr.toNat + m.len.toNat then
      fs.byte m.handle (m.offset + (a - m.addr))
    else
      mem.byte a
  perm := fun a =>
    if m.addr.toNat ≤ a.toNat ∧ a.toNat < m.addr.toNat + m.len.toNat then
      m.prot ||| Runtime.PROT_WRITE
    else
      mem.perm a

end MmapOp

namespace ZeroOp

/-- Zero denotation. In `[z.addr, z.addr + z.len)` `byte` reads `0`;
    `perm` is unchanged (zero runs after mmap, before mprotect — the
    segment is still in the widened-write window). -/
def apply (z : ZeroOp) (mem : Memory) : Memory where
  byte := fun a =>
    if z.addr.toNat ≤ a.toNat ∧ a.toNat < z.addr.toNat + z.len.toNat then
      0
    else
      mem.byte a
  perm := mem.perm

end ZeroOp

namespace StoreOp

/-- Little-endian write denotation. In `[s.addr, s.addr + s.byteLen)`,
    `byte` reads byte `i = a - s.addr` of `s.value`, i.e.,
    `(s.value >>> (8 * i)).toUInt8`. `perm` unchanged. Matches the
    `memcpy(dst, &value, size)` in `runtime/runtime.c` on
    little-endian hardware (every supported arch). -/
def apply (s : StoreOp) (mem : Memory) : Memory where
  byte := fun a =>
    if s.addr.toNat ≤ a.toNat ∧ a.toNat < s.addr.toNat + s.byteLen.toNat then
      let i := a.toNat - s.addr.toNat
      (s.value >>> UInt64.ofNat (8 * i)).toUInt8
    else
      mem.byte a
  perm := mem.perm

end StoreOp

namespace MprotectOp

/-- `mprotect` denotation. `byte` unchanged; in `[m.addr, m.addr +
    m.len)`, `perm` reads `m.prot` (the segment's final permission).
    Outside the range, `perm` is unchanged. -/
def apply (m : MprotectOp) (mem : Memory) : Memory where
  byte := mem.byte
  perm := fun a =>
    if m.addr.toNat ≤ a.toNat ∧ a.toNat < m.addr.toNat + m.len.toNat then
      m.prot
    else
      mem.perm a

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

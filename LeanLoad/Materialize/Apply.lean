/-
Pure denotation of the materialize pipeline over an abstract byte-
level memory model.

The file is laid out bottom-up:

  · `Memory` + `Memory.zero`       — the abstract substrate.
  · `File`                          — frozen file-bytes snapshot.
  · `MmapOp.apply` / `ZeroOp.apply` /
    `StoreOp.apply` / `MprotectOp.apply` —
                                       per-op pure denotation.
  · `SegmentOps.apply` / `ElfOps.apply` /
    `LoadOps.apply`                  — tree-level fold.

`Memory.byte` is total: addresses unmapped by any op return `0`.
The `Reserve.run` contract (kernel-zeroed anon mmap before any
planned op runs) makes this extensional default the right answer
inside the reservation; the soundness theorems quantify there, so
the unmapped-default never gets exercised.

Permissions are not modelled. `MprotectOp.apply` is the identity
on `Memory`; it's kept in the apply chain only for structural
symmetry with `runUnsafe`'s op sequence. Adding perm tracking would
be a `perm : UInt64 → UInt32` second field on `Memory` plus a
`LoadSafe.mprotectsPairwiseDisjoint` extension; both deferred
until a caller needs them.

Address-arithmetic convention: each in-range test is in `Nat` via
`.toNat` (avoids UInt64 wrap). When the test holds, the file-offset
or store-byte-index lookup uses ordinary UInt64 arithmetic, safe
because the in-range bound has already ruled out the wrapping case.
-/

import LeanLoad.Materialize.LoadOps

namespace LeanLoad

-- ============================================================================
-- Memory + File — the abstract substrate `apply` operates over.
-- ============================================================================

/-- Byte-level memory state. `byte` is a total function over
    `UInt64`; unmapped addresses return `0`. -/
structure Memory where
  byte : UInt64 → UInt8
  deriving Nonempty

namespace Memory

/-- Initial state — every byte zero. Stands in for memory prior to
    any kernel mapping. Inside the reservation, `Reserve.run`'s
    anonymous mmap establishes byte = 0; the first ops in each
    segment then refine this state. -/
def zero : Memory := { byte := fun _ => 0 }

@[simp] theorem zero_byte (a : UInt64) : Memory.zero.byte a = 0 := rfl

end Memory

/-- Frozen view of every open file's bytes. Per-handle, per-offset.
    Bytes past EOF read as `0` (matches both `pread` short-read and
    `mmapFile` zero-tail). `Discover` froze every ELF's contents at
    parse time; the snapshot abstracts over the per-section `pread`
    pattern in `Parse.parse` and over the `MAP_PRIVATE` mmap. -/
structure File where
  byte : Runtime.FileHandle → UInt64 → UInt8

-- ============================================================================
-- Per-op denotations. Each lifts its slot record to a `Memory → Memory`.
-- ============================================================================

namespace MmapOp

/-- File-overlay denotation. In `[m.addr, m.addr + m.len)`, `byte`
    reads the corresponding file byte
    `fs.byte m.handle (m.offset + (a - m.addr))`. Outside the range,
    `byte` is unchanged. -/
def apply (fs : File) (m : MmapOp) (mem : Memory) : Memory where
  byte := fun a =>
    if m.addr.toNat ≤ a.toNat ∧ a.toNat < m.addr.toNat + m.len.toNat then
      fs.byte m.handle (m.offset + (a - m.addr))
    else
      mem.byte a

end MmapOp

namespace ZeroOp

/-- Zero denotation. In `[z.addr, z.addr + z.len)` `byte` reads `0`. -/
def apply (z : ZeroOp) (mem : Memory) : Memory where
  byte := fun a =>
    if z.addr.toNat ≤ a.toNat ∧ a.toNat < z.addr.toNat + z.len.toNat then
      0
    else
      mem.byte a

end ZeroOp

namespace StoreOp

/-- Little-endian write denotation. In `[s.addr, s.addr + s.byteLen)`,
    `byte` reads byte `i = a - s.addr` of `s.value`, i.e.,
    `(s.value >>> (8 * i)).toUInt8`. Matches the
    `memcpy(dst, &value, size)` in `runtime/runtime.c` on
    little-endian hardware (every supported arch). -/
def apply (s : StoreOp) (mem : Memory) : Memory where
  byte := fun a =>
    if s.addr.toNat ≤ a.toNat ∧ a.toNat < s.addr.toNat + s.byteLen.toNat then
      let i := a.toNat - s.addr.toNat
      (s.value >>> UInt64.ofNat (8 * i)).toUInt8
    else
      mem.byte a

end StoreOp

namespace MprotectOp

/-- `mprotect` denotation. Identity on `Memory` — the runtime
    `mprotect(2)` changes page permissions, but `Memory` doesn't
    model permissions, so there is no byte-level effect. Defined
    explicitly so `SegmentOps.apply`'s op chain still terminates
    in a `MprotectOp.apply` step that mirrors `runUnsafe`. -/
def apply (_m : MprotectOp) (mem : Memory) : Memory := mem

end MprotectOp

-- ============================================================================
-- Tree-level denotations. Each mirrors the corresponding `runUnsafe`
-- branch in `Materialize/Safety.lean` exactly.
-- ============================================================================

namespace Materialize.SegmentOps

open LeanLoad

/-- Per-segment denotation. Composition order matches
    `SegmentOps.runUnsafe`:
      mmap?  → zero?  → stores (in array order)  → mprotect
    The two `Option` slots default to identity when `none`. The
    trailing `mprotect.apply` is identity, so the result equals
    the post-stores fold. -/
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

open LeanLoad

/-- Per-elf denotation. Folds the segment denotations in declared
    order. -/
def apply (fs : File) (eo : ElfOps n) (mem : Memory) : Memory :=
  eo.segments.foldl (init := mem) fun m so => so.apply fs m

end Materialize.ElfOps

namespace Materialize.LoadOps

open LeanLoad

/-- Top-level denotation. Folds the per-elf denotations in declared
    order (main at index 0). The result is the abstract memory state
    that `LoadOps.runSafe` is axiomatized to realize (see
    `LeanLoad/RuntimeAxiom.lean`). -/
def apply (fs : File) (lo : LoadOps n) (mem : Memory) : Memory :=
  lo.foldl (init := mem) fun m eo => eo.apply fs m

end Materialize.LoadOps

end LeanLoad

/-
Abstract byte-level + permission memory state.

The pure half of the FFI axiom layer. `Memory` is a struct with
two parallel total functions:

  · `byte : UInt64 → UInt8` — byte value at each address.
  · `perm : UInt64 → Perm` — POSIX protection bits at each address.

Both fields are total — unmapped addresses return `0` (zero bytes
+ no permissions), which is the right extensional answer because:

  · Our reservation is a single anonymous mmap block that the
    kernel zero-fills with `PROT_READ | PROT_WRITE` before any
    planned op runs (`Reserve.run`'s contract).
  · Every planned op (`MmapOp`, `ZeroOp`, `StoreOp`, `MprotectOp`)
    lands inside that block.
  · Soundness theorems quantify over addresses inside the
    reservation only, so the unmapped-default-0 case never gets
    exercised.

Why parallel-fields rather than a true region tree:

  · Lookup is O(1) extensional point query, vs O(n) region search.
  · Each `Op.apply` becomes "modify byte/perm in this contiguous
    range, leave the rest" — a structurally clean transformation.
  · The conceptual "segment" of a region-based model is implicit
    in each op's `addr` + `len` fields; the model doesn't need to
    materialise a region list to represent it.
  · A region-tree representation would buy fault-distinction
    (mapped vs unmapped) but at significant proof cost; no
    current theorem requires it.

A region-tree would be the right model if/when we want to prove
"the loader never writes to unmapped memory" (fault-freedom) or
similar properties. For the four byte/perm soundness theorems
(`bytes_preserved`, `bss_zeroed`, `relocs_applied`,
`permissions_correct`), parallel-fields is sufficient and
proof-friendly.

Spec layering:

  · `MmapOp.apply`     — overlay file bytes; widen perm with PROT_WRITE.
  · `ZeroOp.apply`     — clear bytes; perm unchanged.
  · `StoreOp.apply`    — write LE bytes; perm unchanged.
  · `MprotectOp.apply` — bytes unchanged; set perm to `m.prot`.
-/

namespace LeanLoad.Spec

/-- POSIX-style protection bits. Matches `Runtime.PROT_*` constants:
    `PROT_READ = 1`, `PROT_WRITE = 2`, `PROT_EXEC = 4`. -/
abbrev Perm := UInt32

/-- Byte-level memory state with parallel permission tracking.
    Both `byte` and `perm` are total functions over `UInt64`;
    unmapped addresses return `0`. -/
structure Memory where
  byte : UInt64 → UInt8
  perm : UInt64 → Perm
  deriving Nonempty

namespace Memory

/-- Initial state — every byte zero, every address unmapped (perm 0).
    Stands in for memory prior to any kernel mapping. Inside the
    reservation, `Reserve.run`'s anonymous mmap establishes byte = 0
    and perm = PROT_RW; the first ops in each segment then refine
    this state. -/
def zero : Memory := { byte := fun _ => 0, perm := fun _ => 0 }

@[simp] theorem zero_byte (a : UInt64) : Memory.zero.byte a = 0 := rfl
@[simp] theorem zero_perm (a : UInt64) : Memory.zero.perm a = 0 := rfl

end Memory

end LeanLoad.Spec

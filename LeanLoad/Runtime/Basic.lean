/-
Runtime-facing data types.

This module is intentionally free of `@[extern]` declarations. Pure stages such
as `Finalize` import it to build typed operation records without depending on
the IO interpreter.
-/

import LeanLoad.Runtime.File

namespace LeanLoad

namespace Runtime

/-- POSIX `PROT_WRITE` — used to widen a file overlay's initial
   permission so relocation patches can write before the final
   `mprotect` drops the bit. -/
def PROT_WRITE : UInt32 := 2

end Runtime

-- ============================================================================
-- Typed op records — each wraps the FFI signature of one of the runtime
-- operations. `Finalize/LoadOps.lean` assembles the four op kinds into the
-- per-segment tree; `Reserve` is the one-shot anon allocation that bounds every
-- op.
-- ============================================================================

/-- File-backed `MAP_PRIVATE | MAP_FIXED` mmap. -/
structure MmapOp where
  handle : Runtime.File
  addr   : UInt64
  len    : UInt64
  prot   : UInt32
  offset : UInt64

/-- Zero `len` bytes starting at `addr`. -/
structure ZeroOp where
  addr : UInt64
  len  : UInt64

/-- Store the low `size` bytes (4 or 8) of `value` at `addr`. -/
structure StoreOp where
  addr  : UInt64
  size  : UInt8
  value : UInt64

/-- Set protection on `[addr, addr+len)`. -/
structure MprotectOp where
  addr : UInt64
  len  : UInt64
  prot : UInt32

/-- Width of a `StoreOp` as a `UInt64`, for range arithmetic. -/
@[inline] def StoreOp.byteLen (s : StoreOp) : UInt64 := s.size.toUInt64

/-- Anon reservation: address + length + the no-wrap proof every
    downstream safety predicate relies on. Used both for the per-layout
    object reservation and for the loaded program's stack.

    A successful `mmap(MAP_ANONYMOUS)` on Linux always satisfies
    `addr + len < 2^64` (userspace VM is 48-bit), but the FFI layer
    can't prove that to Lean — so `Runtime.Memory.reserve` validates at
    runtime and converts the kernel's guarantee into a Lean proof. -/
structure Reserve where
  addr   : UInt64
  len    : UInt64
  noWrap : addr.toNat + len.toNat < 2 ^ 64

end LeanLoad

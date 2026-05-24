/-
Runtime public core types.

Runtime is the trust seam. This root module contains the pure data types that
earlier stages can mention without importing any
`@[extern]` declarations:

  - `FileRange`, `FileBacking`, `File` - checked byte-source interface.
  - `Reserve` - kernel-picked anonymous reservation witness.
  - `ExecArgs` - final jump arguments.

The submodules provide implementations:
  - `File` - production open/read and in-memory fixtures.
  - `Memory` - C-backed memory effects.
  - `Exec` - constructors and final transfer.
  - `Run` - interpreter for finalized `LoadOps`.
-/

import LeanLoad.Basic

namespace LeanLoad

namespace Runtime

/-- Byte range in an open file, checked against that file's observed size. -/
structure FileRange (fileSize : ByteSize) where
  off      : FileOff
  size     : ByteSize
  inBounds : off.toNat + size.toNat ≤ fileSize.toNat
  deriving Repr

/-- The concrete backing for a `Runtime.File m`. Only fd-backed files can be
    interpreted by `Runtime.Memory.mmapFile` as file-backed mmap sources. -/
inductive FileBacking where
  | fd (fd : UInt32)
  | virtual
  deriving Repr

/-- Open file-like byte source. `size` is captured when the source is created;
    `read` accepts only ranges checked against the observed size. File-backed
    mmap is a memory operation, not part of this read interface. -/
structure File (m : Type → Type := IO) where
  backing  : FileBacking
  size     : ByteSize
  read     : FileRange size → ExceptT String m ByteArray

/-- POSIX `PROT_WRITE` - used to widen a file overlay's initial
   permission so relocation patches can write before the final
   `mprotect` drops the bit. -/
def PROT_WRITE : UInt32 := 2

end Runtime

-- ============================================================================
-- Reservation witness - the one-shot anon allocation that bounds finalized ops.
-- ============================================================================

/-- Anon reservation: address + length + the no-wrap proof every
    downstream safety predicate relies on. Used both for the per-layout
    object reservation and for the loaded program's stack.

    A successful `mmap(MAP_ANONYMOUS)` on Linux always satisfies
    `addr + len < 2^64` (userspace VM is 48-bit), but the FFI layer
    can't prove that to Lean — so `Runtime.Memory.reserve` validates at runtime
    and converts the kernel's guarantee into a Lean proof. -/
structure Reserve where
  addr   : UInt64
  len    : UInt64
  noWrap : addr.toNat + len.toNat < 2 ^ 64

namespace Runtime

/-- Arguments for the final non-returning transfer to the loaded program. -/
structure ExecArgs where
  entry           : UInt64
  programHeaderVa : UInt64
  phent           : UInt64
  phnum           : UInt64
  baseVa          : UInt64
  stackVa         : UInt64
  stackLen        : UInt64
  argv0           : String
  deriving Repr, Inhabited

end Runtime

end LeanLoad

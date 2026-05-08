/-
`MemoryOp` — pure description of every kernel call the loader makes.

Sits between the pure planning stages (`Layout`, `Reloc`, `Init`)
and the IO bookend (`Exec`). Each constructor corresponds 1:1 to an
extern in `Runtime`; `runOp` (in `Exec`) is the only place that
dispatches to externs.

Splitting this out lets:
  - Pure planners emit `Array MemoryOp` — testable by `#guard`-ing
    the emitted op list against expected output.
  - The op list be inspected, printed, or filtered by tools without
    re-running IO.

`mmapStack` (kernel-chosen address) and `execAndJump` (no-return
control transfer) stay outside this op set — they don't fit the
"fire-and-forget" pattern (return values, no-return) and run once
per load as one-shot finalizers.
-/

import LeanLoad.Runtime

namespace LeanLoad

/-- One operation the loader asks the kernel to perform. Pure data;
    `Exec.runOp` interprets each constructor by calling the
    corresponding `Runtime.*` extern. -/
inductive MemoryOp where
  /-- File-backed `MAP_PRIVATE | MAP_FIXED` overlay at `addr` for
      `len` bytes from `handle` at file `offset`, with protection
      `prot`. -/
  | mmapFile (handle : Runtime.FileHandle) (addr len : UInt64)
             (prot : UInt32) (offset : UInt64)
  /-- Anonymous `MAP_FIXED` reservation at `addr` for `len` bytes. -/
  | mmapAnon (addr len : UInt64)
  /-- Zero `len` bytes at `addr`. -/
  | zeroout (addr len : UInt64)
  /-- Set protection on `[addr, addr+len)` to `prot`. -/
  | mprotect (addr len : UInt64) (prot : UInt32)
  /-- Write 8 little-endian bytes of `value` at `addr`. -/
  | patch64 (addr value : UInt64)
  /-- Write 4 little-endian bytes of `value` at `addr`. -/
  | patch32 (addr value : UInt64)
  /-- Call the constructor function at `addr`. -/
  | callCtor (addr : UInt64)

end LeanLoad

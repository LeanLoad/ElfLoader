/-
Trust seam: every `@[extern]` declaration that crosses into the C
shims under `runtime/`. A grep for `@[extern]` outside this file is
a smell.

Three topic groups:
  1. Files (`runtime/file.c`) — opaque `FileHandle` wrapping a kernel
     fd. Used by `Parse.RawElf.parse` (per-section pread) and by
     `Exec.realizeSegment` (file-backed mmap from the already-open fd).
  2. Memory ops (`runtime/region.c`) — mmap variants, mprotect, raw
     writes. All addresses are `UInt64`; the kernel address space is
     the lookup table. There is no Lean-side region handle.
  3. Control transfer (`runtime/exec.c`) — call individual ctors and
     the does-not-return jump that hands control to the loaded image.

The C side picks the `MAP_*` flag set per usage pattern (anonymous,
fixed, stack), so Lean callers don't reason about flag bitmasks.
`PROT_*` bits *do* cross the boundary because the planner reasons
per-segment about R/W/X (gabi 07 § Segment Permissions).

The semantics of each operation match Linux `mmap(2)` /
`mprotect(2)`. Mappings live for the process lifetime; the kernel
reclaims at exit. Audited by inspection (~150 lines of C), not
proven.

Bounds proofs live entirely on the Lean side (`Layout.patch_inRange`
etc.); externs take raw `UInt64` addresses and trust the caller has
done the math correctly. Discipline is enforced in Lean by typed
wrappers in `Layout.Region` (a pure `Segment + base` view) — those
are the "safe" entry points; this module exposes the raw externs.
-/

namespace LeanLoad.Runtime

-- ============================================================================
-- FileHandle — opaque kernel fd. Wraps an `open(2)`'d read-only fd.
-- ============================================================================

private opaque FileHandlePointed : NonemptyType
def FileHandle : Type := FileHandlePointed.type
instance : Nonempty FileHandle := FileHandlePointed.property

@[extern "leanload_open"]
opaque openFile (path : @& String) : IO FileHandle

@[extern "leanload_pread"]
opaque pread (h : @& FileHandle) (offset : UInt64) (len : UInt64) : IO ByteArray

/-- File-backed `MAP_PRIVATE | MAP_FIXED` overlay at `vaddr`. Writes
    to that absolute address range from the file at `offset` with
    final protection `prot`. Returns Unit; the mapping just exists. -/
@[extern "leanload_mmap_file"]
opaque mmap (h : @& FileHandle) (vaddr : UInt64) (len : UInt64)
    (prot : UInt32) (offset : UInt64) : IO Unit

-- ============================================================================
-- Memory ops — raw `UInt64` addresses. Caller has done the math.
-- ============================================================================

/-- Anonymous `MAP_FIXED` reservation at `vaddr` for `len` bytes. -/
@[extern "leanload_mmap_reserve"]
opaque mmapReserve (vaddr : UInt64) (len : UInt64) : IO Unit

/-- Anonymous `MAP_STACK` mapping; kernel chooses the address. Returns
    the chosen base — the caller threads it to `execAndJump`. -/
@[extern "leanload_mmap_stack"]
opaque mmapStack (len : UInt64) : IO UInt64

@[extern "leanload_mprotect"]
opaque mprotect (addr : UInt64) (len : UInt64) (prot : UInt32) : IO Unit

/-- Write 8 little-endian bytes of `value` at `addr`. -/
@[extern "leanload_patch64"]
opaque patch64 (addr : UInt64) (value : UInt64) : IO Unit

/-- Write the low 4 little-endian bytes of `value` at `addr`. -/
@[extern "leanload_patch32"]
opaque patch32 (addr : UInt64) (value : UInt64) : IO Unit

@[extern "leanload_zeroout"]
opaque zeroout (addr : UInt64) (len : UInt64) : IO Unit

-- ============================================================================
-- Control transfer (does not return).
-- ============================================================================

@[extern "leanload_exec_call_ctor"]
opaque callCtor (addr : UInt64) : IO Unit

@[extern "leanload_exec_run"]
opaque execAndJump
  (entry  : UInt64)
  (phdrVa : UInt64)
  (phent  : UInt64)
  (phnum  : UInt64)
  (baseVa : UInt64)
  (stackVa : UInt64)
  (stackLen : UInt64)
  (argv0  : @& String) : IO Unit

-- ============================================================================
-- PROT_* constants (Linux). Kept here because the planner uses
-- `PROT_WRITE` to widen a file-backed segment's initial protection
-- so partial-last-page BSS can be zeroed before `mprotect` drops the
-- bit for read-only segments.
-- ============================================================================

def PROT_WRITE : UInt32 := 2

end LeanLoad.Runtime

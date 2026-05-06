/-
The trust seam: every `@[extern]` declaration that crosses into the
C shims under `runtime/`. A grep for `@[extern]` outside this file
is a smell.

Two topic groups:
  1. Memory regions (`runtime/region.c`) — opaque mmap'd handles
     plus the operations the planner emits (mmap variants,
     mprotect, write, base-address read).
  2. Control transfer (`runtime/exec.c`) — calling individual
     constructors and the does-not-return jump that hands control
     to the loaded image.

The C side picks the `MAP_*` flag set per usage pattern (anonymous,
fixed, stack), so Lean callers don't reason about flag bitmasks.
`PROT_*` bits *do* cross the boundary because the planner reasons
per-segment about R/W/X (gabi 07 § Segment Permissions).

The semantics of each operation match Linux `mmap(2)` /
`mprotect(2)`. Mappings live for the process lifetime; the kernel
reclaims at exit. Audited by inspection (~150 lines of C), not
proven.
-/

namespace LeanLoad.Runtime

-- ============================================================================
-- FileHandle: opaque read-only fd wrapper (`runtime/region.c`).
-- Used for (1) `pread`-based metadata parsing and (2) file-backed
-- `mmap` from already-open fds. Finalizer closes the fd at GC time.
-- ============================================================================

private opaque FileHandlePointed : NonemptyType
def FileHandle : Type := FileHandlePointed.type
instance : Nonempty FileHandle := FileHandlePointed.property

/-- Open a file read-only. The fd lives until the handle is GC'd. -/
@[extern "leanload_filehandle_open_read"]
opaque «open» (path : @& String) : IO FileHandle

/-- Byte size of the underlying file (`fstat`). -/
@[extern "leanload_filehandle_size"]
opaque size (h : @& FileHandle) : IO UInt64

/-- `pread(2)` exactly `len` bytes at `offset` into a fresh `ByteArray`.
    Loops over short reads; throws on error or true EOF mid-buffer. -/
@[extern "leanload_filehandle_pread"]
opaque pread (h : @& FileHandle) (offset : UInt64) (len : USize) : IO ByteArray

/-- File-backed `MAP_PRIVATE | MAP_FIXED` at `vaddr` from this handle.
    Returns a `Region` for the freshly mapped range — one mmap = one
    Region across all variants (anon, stack, file-backed). `prot` is
    final permissions; `offset` and `vaddr` must be page-aligned. -/
@[extern "leanload_filehandle_mmap_at"]
opaque mmapAt (h : @& FileHandle) (vaddr : UInt64) (len : USize) (prot : UInt32)
    (offset : UInt64) : IO Region

-- ============================================================================
-- Region: opaque mmap'd handle (`runtime/region.c`)
-- ============================================================================

private opaque RegionPointed : NonemptyType
def Region : Type := RegionPointed.type
instance : Nonempty Region := RegionPointed.property

/-- `PROT_WRITE` bit, used by Map to widen a file-backed segment's
    initial protection so partial-last-page BSS can be zeroed before
    `mprotectRange` drops the bit for read-only segments. The
    planner-side `Layout.protOfFlags` produces the *final* per-segment
    `PROT_*` value (PF_R/W/X mapped to PROT_READ/WRITE/EXEC). -/
def PROT_WRITE : UInt32 := 2

-- mmap variants. The C shim picks the matching `MAP_*` flag set;
-- Lean code never sees raw flags.

/-- Anonymous private mapping (RW) pinned at `vaddr` (`MAP_FIXED`).
    Used by Map as the per-object reservation at the address Layout
    chose; zero-fills BSS-only pages and inter-segment gaps. -/
@[extern "leanload_region_mmap_anon_fixed"]
opaque mmapAnonFixed (vaddr : UInt64) (len : USize) : IO Region

/-- Anonymous private RW stack mapping (`MAP_STACK`). Used for the
    kernel-style stack of the loaded program; permissions stay RW. -/
@[extern "leanload_region_mmap_stack"]
opaque mmapStack (len : USize) : IO Region

-- Operations on regions.

/-- Change protection of a sub-range. Used when one large region
    holds multiple `PT_LOAD` segments with different permissions. -/
@[extern "leanload_region_mprotect_range"]
opaque mprotectRange (r : @& Region) (offset length : USize) (prot : UInt32) : IO Unit

/-- Write 8 little-endian bytes of `value` to `region` at `offset`.
    Used by `RelocApply` for size-8 relocation patches. -/
@[extern "leanload_region_patch64"]
opaque patch64 (region : @& Region) (offset : USize) (value : UInt64) : IO Unit

/-- Write the low 4 little-endian bytes of `value` to `region` at
    `offset`. Used by `RelocApply` for size-4 relocation patches. -/
@[extern "leanload_region_patch32"]
opaque patch32 (region : @& Region) (offset : USize) (value : UInt64) : IO Unit

/-- Zero `len` bytes in `region` starting at `offset`. Used by
    `MapApply` to clear partial-last-page BSS after a file-backed
    overlay. -/
@[extern "leanload_region_zeroout"]
opaque zeroout (region : @& Region) (offset len : USize) : IO Unit

-- ============================================================================
-- Control transfer (`runtime/exec.c`)
-- ============================================================================

/-- Hand control to a loaded image.

    Builds the kernel-style exec stack on `stack` (argc, argv[],
    envp[], auxv[]), switches SP to it, and jumps to `entry`.
    **Does not return** — the loaded program owns the process.

    Auxv entries supplied:
    - `AT_PHDR` / `AT_PHENT` / `AT_PHNUM` if `phdrVa ≠ 0` (real
      glibc/musl need these for `dl_iterate_phdr` and stack-protector
      setup).
    - `AT_PAGESZ = 4096`.
    - `AT_BASE` if `baseVa ≠ 0` (the dynamic linker base, normally 0
      since we are the loader).
    - `AT_ENTRY = entry`.
    - `AT_RANDOM` pointing at 16 bytes on the stack (deterministic for
      now; satisfies stack canary readers). -/
@[extern "leanload_exec_run"]
opaque execAndJump
  (entry  : UInt64)
  (phdrVa : UInt64)
  (phent  : UInt64)
  (phnum  : UInt64)
  (baseVa : UInt64)
  (stack  : @& Region)
  (argv0  : @& String) : IO Unit

/-- Call a constructor / destructor function by its absolute address.
    Signature per gabi 08: `void (*)(int argc, char **argv, char **envp)`.
    We pass `(0, NULL, NULL)`; freestanding ctors typically ignore them. -/
@[extern "leanload_exec_call_ctor"]
opaque callCtor (addr : UInt64) : IO Unit

end LeanLoad.Runtime

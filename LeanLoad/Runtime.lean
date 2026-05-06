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
-- Region: opaque mmap'd handle (`runtime/region.c`)
-- ============================================================================

private opaque RegionPointed : NonemptyType
def Region : Type := RegionPointed.type
instance : Nonempty Region := RegionPointed.property

-- Protection bits (PROT_*) — first-class because the planner
-- reasons about per-segment R/W/X.

def PROT_NONE  : UInt32 := 0
def PROT_READ  : UInt32 := 1
def PROT_WRITE : UInt32 := 2
def PROT_EXEC  : UInt32 := 4

#guard PROT_READ + PROT_WRITE + PROT_EXEC = 7

-- mmap variants. The C shim picks the matching `MAP_*` flag set;
-- Lean code never sees raw flags.

/-- Anonymous private mapping (RW); kernel chooses the address. Used
    for ET_DYN whole-object regions. The caller `mprotect`s to the
    final per-segment permissions after copying bytes in. -/
@[extern "leanload_region_mmap_anon"]
opaque mmapAnon (len : USize) : IO Region

/-- Anonymous private mapping (RW) pinned at `vaddr` (`MAP_FIXED`).
    Used for ET_EXEC per-mapping placement at link-time-fixed
    addresses. Caller `mprotect`s after writing. -/
@[extern "leanload_region_mmap_anon_fixed"]
opaque mmapAnonFixed (vaddr : UInt64) (len : USize) : IO Region

/-- Anonymous private RW stack mapping (`MAP_STACK`). Used for the
    kernel-style stack of the loaded program; permissions stay RW. -/
@[extern "leanload_region_mmap_stack"]
opaque mmapStack (len : USize) : IO Region

-- Operations on regions.

/-- Change protection of the entire region. -/
@[extern "leanload_region_mprotect"]
opaque mprotect (r : @& Region) (prot : UInt32) : IO Unit

/-- Change protection of a sub-range. Used when one large region
    holds multiple `PT_LOAD` segments with different permissions. -/
@[extern "leanload_region_mprotect_range"]
opaque mprotectRange (r : @& Region) (offset length : USize) (prot : UInt32) : IO Unit

/-- Copy bytes from `src` into the region starting at `offset`. -/
@[extern "leanload_region_write"]
opaque write (r : @& Region) (offset : USize) (src : @& ByteArray) : IO Unit

/-- Base virtual address of the region (where the kernel actually placed it). -/
@[extern "leanload_region_base"]
opaque base (r : @& Region) : UInt64

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

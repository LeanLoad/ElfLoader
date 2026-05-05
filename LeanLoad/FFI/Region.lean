/-
FFI: memory regions backed by `mmap`.

A `Region` is an opaque handle for a foreign-owned `mmap`'d range.
The finalizer in `runtime/region.c` calls `munmap` when the refcount
drops to zero, so callers do not need to release explicitly.
-/

namespace LeanLoad.FFI.Region

private opaque RegionPointed : NonemptyType
def Region : Type := RegionPointed.type
instance : Nonempty Region := RegionPointed.property

-- ============================================================================
-- Constants — Linux <sys/mman.h>
-- ============================================================================

-- Protection bits (PROT_*)
def PROT_NONE  : UInt32 := 0
def PROT_READ  : UInt32 := 1
def PROT_WRITE : UInt32 := 2
def PROT_EXEC  : UInt32 := 4

-- Mapping flags (MAP_*)
def MAP_PRIVATE         : UInt32 := 0x02
def MAP_FIXED           : UInt32 := 0x10
def MAP_ANONYMOUS       : UInt32 := 0x20
def MAP_FIXED_NOREPLACE : UInt32 := 0x100000

#guard PROT_READ + PROT_WRITE + PROT_EXEC = 7

-- ============================================================================
-- Externs
-- ============================================================================

/-- Allocate a fresh `mmap`'d region.
    `vaddr = 0` lets the kernel choose an address; otherwise the request
    is honoured per `flags` (typically `MAP_FIXED` or `MAP_FIXED_NOREPLACE`). -/
@[extern "leanload_region_mmap"]
opaque mmap (vaddr : UInt64) (len : USize) (prot flags : UInt32) : IO Region

/-- Change protection of the entire region. -/
@[extern "leanload_region_mprotect"]
opaque mprotect (r : @& Region) (prot : UInt32) : IO Unit

/-- Change protection of a sub-range. Used when one large region holds
    multiple `PT_LOAD` segments with different permissions. -/
@[extern "leanload_region_mprotect_range"]
opaque mprotectRange (r : @& Region) (offset length : USize) (prot : UInt32) : IO Unit

/-- Copy bytes from `src` into the region starting at `offset`. -/
@[extern "leanload_region_write"]
opaque write (r : @& Region) (offset : USize) (src : @& ByteArray) : IO Unit

/-- Base virtual address of the region (where the kernel actually placed it). -/
@[extern "leanload_region_base"]
opaque base (r : @& Region) : UInt64

end LeanLoad.FFI.Region

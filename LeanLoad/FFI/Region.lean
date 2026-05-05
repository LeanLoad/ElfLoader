/-
FFI: memory regions backed by `mmap`.

A `Region` is an opaque handle for a foreign-owned `mmap`'d range.
The C shim picks the `MAP_*` flag set per usage pattern (anonymous,
anonymous fixed, anonymous stack), so Lean callers don't reason about
flag bitmasks. `prot` (R/W/X) does cross the boundary because the
planner tracks per-segment permissions (gabi 07 § Segment Permissions).

The semantics of each operation matches Linux `mmap(2)` / `mprotect(2)`.

Mappings live for the process lifetime; the kernel reclaims at exit.
-/

namespace LeanLoad.FFI.Region

private opaque RegionPointed : NonemptyType
def Region : Type := RegionPointed.type
instance : Nonempty Region := RegionPointed.property

-- ============================================================================
-- Protection bits (PROT_*) — these are first-class because the
-- planner reasons about per-segment R/W/X.
-- ============================================================================

def PROT_NONE  : UInt32 := 0
def PROT_READ  : UInt32 := 1
def PROT_WRITE : UInt32 := 2
def PROT_EXEC  : UInt32 := 4

#guard PROT_READ + PROT_WRITE + PROT_EXEC = 7

-- ============================================================================
-- mmap variants. The C shim picks the matching `MAP_*` flag set;
-- Lean code never sees them.
-- ============================================================================

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

-- ============================================================================
-- Other operations on regions
-- ============================================================================

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

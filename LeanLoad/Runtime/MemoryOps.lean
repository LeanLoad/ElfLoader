/-
Memory runtime capability.

`MemoryOps` interprets the finalized load plan: allocate the reservation, map
file-backed pages, clear BSS tails, apply relocation stores, and set final
permissions. The IO instance is the trusted FFI boundary for memory operations.
-/

import LeanLoad.Runtime.Basic

namespace LeanLoad

namespace Runtime

/-- Memory operations needed to realize a finalized load plan. -/
structure MemoryOps (m : Type → Type) where
  reserve  : (len : UInt64) → m { r : LeanLoad.Reserve // r.len = len }
  mmapFile : File → UInt64 → UInt64 → UInt32 → UInt64 → m Unit
  zero     : UInt64 → UInt64 → m Unit
  store    : UInt64 → UInt8 → UInt64 → m Unit
  mprotect : UInt64 → UInt64 → UInt32 → m Unit

namespace MemoryOps

/-- File-backed `MAP_PRIVATE | MAP_FIXED` mmap at `eaddr`.
    Replaces whatever was at `[eaddr, eaddr+len)` (intentionally — in our design
    that's the kernel-picked anon reservation). -/
@[extern "leanload_mmap_file"]
private opaque mmapFileFd (fd : UInt32) (eaddr : UInt64) (len : UInt64)
    (prot : UInt32) (offset : UInt64) : IO Unit

/-- Kernel-picked anon mapping. `mmap(NULL, len, PROT_READ | PROT_WRITE,
    MAP_PRIVATE | MAP_ANONYMOUS, …)` — kernel returns the chosen base,
    guaranteed disjoint from any existing mapping in the host process. -/
@[extern "leanload_mmap_anon"]
private opaque mmapAnon (len : UInt64) : IO UInt64

@[extern "leanload_mprotect"]
private opaque mprotectRaw (addr : UInt64) (len : UInt64) (prot : UInt32) : IO Unit

/-- Store the low 4 or 8 little-endian bytes of `value` at `addr`, selected by
    `size` (4 or 8). Used for relocation patches. -/
@[extern "leanload_store"]
private opaque storeRaw (addr : UInt64) (size : UInt8) (value : UInt64) : IO Unit

/-- Zero `len` bytes starting at `addr`. Used for the partial-page BSS tail past
    `filesz` on a file mmap's last page. -/
@[extern "leanload_zero"]
private opaque zeroRaw (addr : UInt64) (len : UInt64) : IO Unit

/-- Production memory ops backed by the C runtime. -/
def io : MemoryOps IO :=
  { reserve := fun len => do
      let addr ← mmapAnon len
      if h : addr.toNat + len.toNat < 2 ^ 64 then
        return ⟨⟨addr, len, h⟩, rfl⟩
      else
        throw (IO.userError s!"Runtime.MemoryOps.reserve returned wrapping reservation \
          (addr=0x{addr.toNat}, len=0x{len.toNat})")
    mmapFile := fun f addr len prot offset => mmapFileFd f.fd addr len prot offset
    zero := zeroRaw
    store := storeRaw
    mprotect := mprotectRaw }

end MemoryOps

end Runtime

end LeanLoad

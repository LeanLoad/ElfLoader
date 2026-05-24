/-
Memory runtime capability.

`Memory` interprets the finalized load plan: allocate the reservation, map
file-backed pages, clear BSS tails, apply relocation stores, and set final
permissions. The IO instance is the trusted FFI boundary for memory operations.
-/

import LeanLoad.Runtime

namespace LeanLoad

namespace Runtime

namespace Memory

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

@[extern "leanload_mmap_file"]
private opaque mmapFileFd (fd : UInt32) (eaddr : UInt64) (len : UInt64)
    (prot : UInt32) (offset : UInt64) : IO Unit

/-- Production memory operations backed by the C runtime. -/
def io : Memory IO :=
  { reserve := fun len => do
      let addr ← mmapAnon len
      if h : addr.toNat + len.toNat < 2 ^ 64 then
        return ⟨⟨addr, len, h⟩, rfl⟩
      else
        throw (IO.userError s!"Runtime.Memory.reserve returned wrapping reservation \
          (addr=0x{addr.toNat}, len=0x{len.toNat})")
    mmapFile := fun f addr len prot offset =>
      match f.backing with
      | .fd fd => mmapFileFd fd addr len prot offset
      | .virtual =>
          throw (IO.userError "Runtime.Memory.io cannot mmap a virtual Runtime.File")
    zero := zeroRaw
    store := storeRaw
    mprotect := mprotectRaw }

end Memory

end Runtime

end LeanLoad

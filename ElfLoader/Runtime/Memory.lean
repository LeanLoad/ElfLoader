/-
Memory runtime effects.

These functions are the trusted FFI boundary for finalized load plans: allocate
the reservation, map file-backed pages, clear BSS tails, apply relocation stores,
and set final permissions. Safety properties are proved over `Finalize.LoadOps`;
this module only interprets already-witnessed addresses.
-/

import ElfLoader.Runtime

namespace ElfLoader

namespace Runtime

namespace Memory

/-- Kernel-picked anon mapping. `mmap(NULL, len, PROT_READ | PROT_WRITE,
    MAP_PRIVATE | MAP_ANONYMOUS, …)` — kernel returns the chosen base,
    guaranteed disjoint from any existing mapping in the host process. -/
@[extern "elfloader_mmap_anon"]
private opaque mmapAnon (len : UInt64) : IO UInt64

@[extern "elfloader_mprotect"]
private opaque mprotectRaw (addr : UInt64) (len : UInt64) (prot : UInt32) : IO Unit

/-- Store the low 4 or 8 little-endian bytes of `value` at `addr`, selected by
    `size` (4 or 8). Used for relocation patches. -/
@[extern "elfloader_store"]
private opaque storeRaw (addr : UInt64) (size : UInt8) (value : UInt64) : IO Unit

/-- Zero `len` bytes starting at `addr`. Used for the partial-page BSS tail past
    `filesz` on a file mmap's last page. -/
@[extern "elfloader_zero"]
private opaque zeroRaw (addr : UInt64) (len : UInt64) : IO Unit

@[extern "elfloader_mmap_file"]
private opaque mmapFileFd (fd : UInt32) (eaddr : UInt64) (len : UInt64)
    (prot : UInt32) (offset : UInt64) : IO Unit

/-- Reserve an anonymous RW mapping and return the kernel-chosen non-wrapping range. -/
def reserve (len : UInt64) : IO { r : ElfLoader.Reserve // r.len = len } := do
  let addr ← mmapAnon len
  if h : addr.toNat + len.toNat < 2 ^ 64 then
    return ⟨⟨addr, len, h⟩, rfl⟩
  else
    throw (IO.userError s!"Runtime.Memory.reserve returned wrapping reservation \
      (addr=0x{addr.toNat}, len=0x{len.toNat})")

/-- File-backed `MAP_PRIVATE | MAP_FIXED` mmap for one finalized segment overlay. -/
def mmapFile (f : File) (addr len : UInt64) (prot : UInt32) (offset : UInt64) : IO Unit :=
  match f.backing with
  | .fd fd => mmapFileFd fd addr len prot offset
  | .virtual =>
      throw (IO.userError "Runtime.Memory.mmapFile cannot mmap a virtual Runtime.File")

/-- Zero `len` bytes starting at `addr`. -/
def zero (addr len : UInt64) : IO Unit :=
  zeroRaw addr len

/-- Store the low 4 or 8 bytes of `value` at `addr`. -/
def store (addr : UInt64) (size : UInt8) (value : UInt64) : IO Unit :=
  storeRaw addr size value

/-- Set protection on `[addr, addr+len)`. -/
def mprotect (addr len : UInt64) (prot : UInt32) : IO Unit :=
  mprotectRaw addr len prot

end Memory

end Runtime

end ElfLoader

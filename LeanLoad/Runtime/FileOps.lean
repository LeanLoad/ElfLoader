/-
File runtime capability.

`FileOps` is the small filesystem-like surface used by discovery and parsing:
resolve/open an object by loader search rules, observe its size, and read a
byte range. The IO instance is the only place that crosses into `Runtime.c` for
file operations.
-/

import LeanLoad.Runtime.Basic

namespace LeanLoad

namespace Runtime

/-- File operations over an abstract handle. `openByName` follows loader search
    semantics; `pread` is raw and range-checked by the IO implementation. -/
structure FileOps (m : Type → Type) (Handle : Type) where
  openByName : String → Option String → m (Option Handle)
  fileSize   : Handle → UInt64
  pread      : Handle → UInt64 → UInt64 → m ByteArray

namespace FileOps

/-- Resolve a `DT_NEEDED` soname against `LD_LIBRARY_PATH` + the given `runpath`,
    open the resulting file `RDONLY | CLOEXEC`, and return the fd.

    Search rules (gabi 08 § Shared Object Dependencies):
      1. If `soname` contains '/', open as a literal path.
      2. Else search `LD_LIBRARY_PATH` (`:`-separated; first hit wins).
      3. Else search `runpath` (if `some`).
      4. Else `none`.

    Implementation lives in `Runtime.c` — keeps path splitting and `getenv` out
    of Lean. -/
@[extern "leanload_open_by_name"]
private opaque openByNameFd (soname : @& String) (runpath : @& Option String) :
    IO (Option UInt32)

@[extern "leanload_file_size"]
private opaque fileSizeFd (fd : UInt32) : IO UInt64

@[extern "leanload_pread"]
private opaque preadFd (fd : UInt32) (offset : UInt64) (len : UInt64) : IO ByteArray

/-- Production file ops backed by the C runtime. -/
def io : FileOps IO File :=
  { openByName := fun soname runpath => do
      match ← openByNameFd soname runpath with
      | none    => pure none
      | some fd =>
          let size ← fileSizeFd fd
          pure (some { fd, size })
    fileSize := fun f => f.size
    pread := fun f offset len => do
      if _h : f.containsRange offset len then
       preadFd f.fd offset len
      else
       throw (IO.userError s!"pread out of bounds: offset 0x{offset.toNat}, \
         len {len.toNat}, file size {f.size.toNat}") }

end FileOps

end Runtime

end LeanLoad

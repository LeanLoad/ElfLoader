/-
File byte source boundary.

Opening is separate from reading: path search produces a `Runtime.File IO`, and
an open file already carries the observed file size. Pure fixtures use the same
`File m` interface with `m = Id`.
-/

import LeanLoad.Basic

namespace LeanLoad

namespace Runtime

/-- Byte range in an open file, checked against that file's observed size. -/
structure FileRange (fileSize : ByteSize) where
  off      : FileOff
  size     : ByteSize
  inBounds : off.toNat + size.toNat ≤ fileSize.toNat
  deriving Repr

/-- The concrete backing for a `Runtime.File m`. Only fd-backed files can be
    interpreted by `Runtime.Memory.io` as file-backed mmap sources. -/
inductive FileBacking where
  | fd (fd : UInt32)
  | virtual
  deriving Repr

/-- Open file-like byte source. `size` is captured when the source is created;
    `read` accepts only ranges checked against that observed size. File-backed
    mmap is a memory operation, not part of this read interface. -/
structure File (m : Type → Type := IO) where
  backing  : FileBacking
  size     : ByteSize
  read     : FileRange size → ExceptT String m ByteArray

namespace File

instance : Repr (File m) where
  reprPrec file _ :=
    "{ backing := " ++ repr file.backing ++
      ", size := " ++ repr file.size ++ ", read := <function> }"

/-- Resolve a `DT_NEEDED` soname against `LD_LIBRARY_PATH` + the given `runpath`,
    open the resulting file `RDONLY | CLOEXEC`, and return the open file.

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

/-- Build the public `Runtime.File IO` value from the private kernel descriptor. -/
private def ofFd (fd : UInt32) (size : UInt64) : File :=
  { backing := .fd fd
    size := ⟨size⟩
    read := fun range => do
      let bytes ← preadFd fd range.off.val range.size.val
      if bytes.size == range.size.toNat then
        pure bytes
      else
        throw s!"pread short read: offset 0x{range.off.toNat}, requested \
          {range.size.toNat} bytes, got {bytes.size}" }

/-- Production path search/open. The returned `Runtime.File` includes the
    observed file size immediately after open. -/
def openByName (soname : String) (runpath : Option String) : IO (Option File) := do
  match ← openByNameFd soname runpath with
  | none    => pure none
  | some fd =>
      let size ← fileSizeFd fd
      pure (some (ofFd fd size))

/-- In-memory file source for pure fixtures and tests. -/
def ofByteArray (bytes : ByteArray) : File Id :=
  { backing := .virtual
    size := ByteSize.ofNat bytes.size
    read := fun range =>
      pure <| bytes.extract range.off.toNat (range.off.toNat + range.size.toNat) }

end File

end Runtime

end LeanLoad

/-
File byte source boundary.

Opening is separate from reading: path search produces a `Runtime.File IO`, and
an open file already carries the observed file size. Pure fixtures use the same
`File m` interface with `m = Id`.
-/

import ElfLoader.Runtime

namespace ElfLoader

namespace Runtime

namespace File

instance : Repr (File m) where
  reprPrec file _ :=
    "{ backing := " ++ repr file.backing ++
      ", size := " ++ repr file.size ++ ", read := <function> }"

@[extern "elfloader_open_path"]
private opaque openPathFd (path : @& String) : IO (Option UInt32)

@[extern "elfloader_file_size"]
private opaque fileSizeFd (fd : UInt32) : IO UInt64

@[extern "elfloader_pread"]
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

/-- Open one exact path `RDONLY | CLOEXEC`. Dependency search policy is
    intentionally not in C; Discover computes candidate paths before trying exact
    opens. -/
def openPath (path : String) : IO (Option File) := do
  match ← openPathFd path with
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

end ElfLoader

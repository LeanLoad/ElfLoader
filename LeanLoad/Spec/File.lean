/-
File-bytes snapshot.

A `File` freezes the on-disk contents of every open file at a
single conceptual moment — the moment `Discover` parsed each ELF.
Indexed by `(FileHandle, fileOffset)` so per-file overlays in
`MmapOp.apply` can look up the source byte at `(m.handle, m.offset
+ k)`.

Why a separate snapshot type rather than threading raw bytes
through the parser:

  · `Parse.parse` does per-section `pread` calls into private
    `ByteArray`s; no whole-file array is ever constructed. The
    snapshot abstracts over that, so the spec doesn't need to
    follow the parser's section-by-section view.

  · The `pread` FFI is the trust seam for file I/O. Axiomatising
    "`pread h off len` returns the snapshot's bytes at `[off,
    off+len)`" is the smallest discharge of that seam — much
    smaller than reasoning about per-section reads.

  · The snapshot is *frozen*. It does not change during the load.
    The host process's trust assumption "no concurrent file
    mutation during materialize" (docs/design.md § Trust
    assumptions) is what justifies this; under that assumption,
    every `pread` and every `mmapFile MAP_PRIVATE` observes the
    same bytes for the same offset.

Bytes outside the file (offsets ≥ file length) read as `0`. Real
`pread` returns short-read or EOF; an `mmapFile` past EOF yields
a zero-filled tail (Linux `mmap(2)`). Returning `0` extensionally
matches both cases for the *byte-equality* statements the
soundness theorems care about, while avoiding the bookkeeping of
a length-per-handle.
-/

import LeanLoad.Runtime

namespace LeanLoad.Spec

/-- Frozen view of every open file's bytes. Per-handle, per-offset.
    Bytes past EOF read as `0` (matches both `pread` short-read and
    `mmapFile` zero-tail). -/
structure File where
  byte : Runtime.FileHandle → UInt64 → UInt8

end LeanLoad.Spec

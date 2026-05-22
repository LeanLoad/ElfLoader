/-
File-reader abstraction for `Parse.parse`.

`parse` doesn't care *how* a section's bytes arrive — only that for
each `(FileOff, ByteSize)` it can get back a `ByteArray`. `FileReader`
captures exactly that contract, monad-polymorphic over `m`:

  • Production reader (`Runtime.fileReader f`) — backed by
    `Runtime.pread` over an open kernel `Runtime.File`. Runs in `IO`.

  • Pure reader (`pureReader bytes`) — slices a single in-memory
    `ByteArray`. Runs in `Id`. Lets the fixture exercise the
    *production* `parse` over its hand-crafted bytes instead of
    maintaining a parallel walk.

Errors flow through `ExceptT String m`: the reader does the I/O (`m`);
`readSlice` first checks `(FileOff, ByteSize)` into a `FileRange` against the
known file size, then rejects short/oversized reads before `Parser.run`.
Decode failures get caught and rethrown as the ExceptT error.
-/

import LeanLoad.Parse.Address
import LeanLoad.Parse.Decode
import LeanLoad.Runtime

namespace LeanLoad.Parse

/-- Read `(offset, length)` → bytes in some monad `m`. The raw reader
    delivers bytes; `readSlice` below turns that into a witnessed
    exact-length file slice. -/
structure FileReader (m : Type → Type) where
  /-- Observed file size. `readSlice` rejects any range not fully contained in
      `[0, fileSize)` before calling `read`. -/
  fileSize : UInt64
  read : (off : FileOff) → (len : ByteSize) → FileRange fileSize off len → m ByteArray

/-- Production reader backed by bounded `Runtime.pread`. -/
def Runtime.fileReader (f : LeanLoad.Runtime.File) : FileReader IO :=
  { fileSize := f.size
    read := fun off len _span => LeanLoad.Runtime.pread f off.val len.val }

/-- Pure reader over an in-memory `ByteArray`. Out-of-range reads
    return a truncated slice — the downstream `Parser` then fails
    with its own EOF message, so the truncation is observable, not
    silently masked. Used by `Elf.Example.fixture` to run the
    production `parse` over the hand-crafted fixture bytes. -/
def pureReader (bytes : ByteArray) : FileReader Id :=
  { fileSize := UInt64.ofNat bytes.size
    read := fun off len _span =>
      let o := off.toNat
      let n := len.toNat
      bytes.extract o (min (o + n) bytes.size) }

/-- Bytes read for one requested file range, witnessed to have exactly
    the requested length. This is the Parse-layer substitute for a
    global file-size proof: any out-of-bounds regular-file read must
    fail or produce a non-exact slice before bytes are decoded. -/
structure FileSlice (fileSize : UInt64) (off : FileOff) (len : ByteSize) where
  span : FileRange fileSize off len
  bytes : ByteArray
  size_eq : bytes.size = len.toNat

namespace FileSlice

/-- Package raw bytes into a `FileSlice` only when the reader delivered
    exactly the requested byte count. -/
def ofBytes {fileSize : UInt64} {off : FileOff} {len : ByteSize}
    (span : FileRange fileSize off len) (bytes : ByteArray) :
    Except String (FileSlice fileSize off len) :=
  if h : bytes.size = len.toNat then
    .ok { span, bytes, size_eq := h }
  else
    .error s!"read at file offset 0x{off.toNat} requested {len.toNat} bytes, \
      got {bytes.size}"

private def guardRange2 : FileRange (2 : UInt64) (0 : FileOff) (2 : ByteSize) :=
  { inFile := by decide }

private def guardRange3 : FileRange (3 : UInt64) (0 : FileOff) (3 : ByteSize) :=
  { inFile := by decide }

#guard
  match ofBytes guardRange2 ⟨#[0x1, 0x2]⟩ with
  | .ok s    => s.bytes.size == 2
  | .error _ => false

#guard
  match ofBytes guardRange3 ⟨#[0x1, 0x2]⟩ with
  | .ok _    => false
  | .error _ => true

end FileSlice

/-- Read a file range and carry the exact-length witness forward to
    the parser boundary. -/
def readSlice [Monad m] (r : FileReader m)
    (off : FileOff) (len : ByteSize) : ExceptT String m (FileSlice r.fileSize off len) := do
  if h : off.toNat + len.toNat ≤ r.fileSize.toNat then
    let span : FileRange r.fileSize off len := { inFile := h }
    let bytes ← (r.read off len span : m ByteArray)
    match FileSlice.ofBytes span bytes with
    | .ok slice => pure slice
    | .error e  => throw e
  else
    throw s!"read at file offset 0x{off.toNat} requested {len.toNat} bytes, \
      past file size {r.fileSize.toNat}"

/-- Read `(off, len)` via the reader and decode the result with
    `parser`. The Parser's cursor starts at 0 within the returned
    slice — section-local, not file-absolute. Decode failure throws
    the parser's error string into `ExceptT String m`. -/
def parseAt [Monad m] (r : FileReader m)
    (off : FileOff) (len : ByteSize) (parser : Parser α) : ExceptT String m α := do
  let slice ← readSlice r off len
  match Parser.run slice.bytes parser with
  | .ok v    => pure v
  | .error e => throw e

end LeanLoad.Parse

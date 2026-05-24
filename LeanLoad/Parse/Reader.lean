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

Errors flow through `ExceptT String m`: `checkRange` is the raw-metadata
boundary that turns `(FileOff, ByteSize)` into a `FileRange`; `readRange`
reads the witnessed range and verifies exact byte count. Decoding is deliberately
kept in the parse orchestration layer.
-/

import LeanLoad.Parse.Address
import LeanLoad.Runtime

namespace LeanLoad.Parse

/-- Read bytes in some monad `m`. The raw reader delivers bytes only for ranges
    already witnessed to fit in the observed file. -/
structure FileReader (m : Type → Type) where
  /-- Observed file size. `checkRange` rejects any range not fully contained in
      `[0, fileSize)` before calling `read`. -/
  fileSize : UInt64
  read : {off : FileOff} → {len : ByteSize} → FileRange fileSize off len → m ByteArray

/-- Production reader backed by bounded `Runtime.pread`. -/
def Runtime.fileReader (f : LeanLoad.Runtime.File) : FileReader IO :=
  { fileSize := f.size
    read := fun {off} {len} _span => LeanLoad.Runtime.pread f off.val len.val }

/-- Pure reader over an in-memory `ByteArray`. Used by `Parse.Examples.fixture`
    to run the production `parse` over the hand-crafted fixture bytes. -/
def pureReader (bytes : ByteArray) : FileReader Id :=
  { fileSize := UInt64.ofNat bytes.size
    read := fun {off} {len} _span =>
      let o := off.toNat
      let n := len.toNat
      bytes.extract o (o + n) }

private def guardRange2 : FileRange (2 : UInt64) (0 : FileOff) (2 : ByteSize) :=
  { inFile := by decide }

private def guardRange3 : FileRange (3 : UInt64) (0 : FileOff) (3 : ByteSize) :=
  { inFile := by decide }

#guard
  ((pureReader ⟨#[0x1, 0x2]⟩).read guardRange2).size == 2

#guard
  ((pureReader ⟨#[0x1, 0x2, 0x3]⟩).read guardRange3).size == 3

/-- Raw-metadata boundary: check an offset/size pair against the observed file
    size and return the witnessed `FileRange`. Prefer passing the returned
    witness through internal APIs instead of the raw pair. -/
def checkRange (r : FileReader m) (off : FileOff) (len : ByteSize) :
    Except String (FileRange r.fileSize off len) :=
  if h : off.toNat + len.toNat ≤ r.fileSize.toNat then
    .ok { inFile := h }
  else
    .error s!"read at file offset 0x{off.toNat} requested {len.toNat} bytes, \
      past file size {r.fileSize.toNat}"

/-- Read bytes from an already-checked file range. The returned `ByteArray` is
    checked to have exactly the requested length. -/
def readRange [Monad m] (r : FileReader m)
    {off : FileOff} {len : ByteSize} (span : FileRange r.fileSize off len) :
    ExceptT String m ByteArray := do
  let bytes ← (r.read span : m ByteArray)
  if bytes.size == len.toNat then
    pure bytes
  else
    throw s!"read at file offset 0x{off.toNat} requested {len.toNat} bytes, \
      got {bytes.size}"

end LeanLoad.Parse

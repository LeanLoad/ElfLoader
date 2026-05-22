/-
File-reader abstraction for `Parse.RawElf.parse`.

`parse` doesn't care *how* a section's bytes arrive — only that for
each `(offset, length)` it can get back a `ByteArray`. `FileReader`
captures exactly that contract, monad-polymorphic over `m`:

  • Production reader (`Runtime.fileReader h`) — backed by
    `Runtime.pread` over an open kernel `FileHandle`. Runs in `IO`.

  • Pure reader (`pureReader bytes`) — slices a single in-memory
    `ByteArray`. Runs in `Id`. Lets the fixture exercise the
    *production* `parse` over its hand-crafted bytes instead of
    maintaining a parallel walk.

Errors flow through `ExceptT String m`: the reader does the I/O
(`m`); `Parser.run` decode-failures get caught and rethrown as the
ExceptT error.
-/

import LeanLoad.Parse.Decode
import LeanLoad.Runtime

namespace LeanLoad.Parse

/-- Read `(offset, length)` → bytes in some monad `m`. The only
    contract is byte delivery; bounds errors live in `m`'s own
    failure mechanism (IO throws; `Id` truncates → Parser EOFs). -/
structure FileReader (m : Type → Type) where
  read : UInt64 → UInt64 → m ByteArray

/-- Production reader backed by `Runtime.pread`. Each call is one
    `pread(2)` syscall on the open `FileHandle`. -/
def Runtime.fileReader (h : LeanLoad.Runtime.FileHandle) : FileReader IO :=
  { read := LeanLoad.Runtime.pread h }

/-- Pure reader over an in-memory `ByteArray`. Out-of-range reads
    return a truncated slice — the downstream `Parser` then fails
    with its own EOF message, so the truncation is observable, not
    silently masked. Used by `RawElf.fixture` to run the production
    `parse` over the hand-crafted fixture bytes. -/
def pureReader (bytes : ByteArray) : FileReader Id :=
  { read := fun off len =>
      let o := off.toNat
      let n := len.toNat
      bytes.extract o (min (o + n) bytes.size) }

/-- Read `(off, len)` via the reader and decode the result with
    `parser`. The Parser's cursor starts at 0 within the returned
    slice — section-local, not file-absolute. Decode failure throws
    the parser's error string into `ExceptT String m`. -/
def parseAt [Monad m] (r : FileReader m)
    (off len : UInt64) (parser : Parser α) : ExceptT String m α := do
  let bytes ← (r.read off len : m ByteArray)
  match Parser.run bytes parser with
  | .ok v    => pure v
  | .error e => throw e

end LeanLoad.Parse

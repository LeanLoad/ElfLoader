/-
Checked ELF parser entry points.

The implementation is split under `Parse/Elf/`:
  - `Checked` defines the checked `Elf` type.
  - `RawImage` follows file offsets and dynamic-table virtual addresses to build a
    transient byte staging image.
  - `Check` validates the staging image into the witness-carrying `Elf`.
-/

import LeanLoad.Parse.Elf.Checked
import LeanLoad.Parse.Elf.RawImage
import LeanLoad.Parse.Elf.Check
import LeanLoad.Runtime

namespace LeanLoad.Parse

open LeanLoad

/-- Monad-polymorphic checked parse. The `FileReader m` abstracts byte
    delivery; all parse and validation errors flow through `ExceptT`. -/
def parseM [Monad m] (r : FileReader m) : ExceptT String m Elf := do
  let image ← Elf.readImageM r
  match Elf.checkImage image with
  | .ok elf  => pure elf
  | .error e => throw e

/-- Production entry point: parse and check an open file. -/
def parse (f : Runtime.File) : IO Elf := do
  match ← (parseM (Runtime.fileReader f)).run with
  | .ok elf  => pure elf
  | .error e => throw (IO.userError e)

end LeanLoad.Parse

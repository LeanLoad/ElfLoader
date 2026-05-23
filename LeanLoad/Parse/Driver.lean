/-
Top-level Parse driver.

This module is intentionally thin: byte decoding lives under `Decode`, file
slice reads live in `Reader`, dynamic staging lives under `Dynamic`, and checked
ELF construction lives in `Elf`. The driver only sequences those stages.
-/

import LeanLoad.Parse.Dynamic.Read
import LeanLoad.Parse.Elf
import LeanLoad.Runtime

namespace LeanLoad.Parse

/-- Monad-polymorphic checked parse. The `FileReader m` abstracts byte delivery;
    all parse and validation errors flow through `ExceptT`. -/
def parseM [Monad m] (r : FileReader m) : ExceptT String m Elf := do
  let image ← Dynamic.readM r
  match Elf.ofDynamic image with
  | .ok elf  => pure elf
  | .error e => throw e

/-- Production entry point: parse and check an open file. -/
def parse (f : Runtime.File) : IO Elf := do
  match ← (parseM (Runtime.fileReader f)).run with
  | .ok elf  => pure elf
  | .error e => throw (IO.userError e)

end LeanLoad.Parse

/-
Byte-level parser for the `.dynamic` array.
Spec types live in `LeanLoad.Spec.Dynamic`.
-/

import LeanLoad.Parse.Bytes
import LeanLoad.Spec.Dynamic

namespace LeanLoad.Parse.Dynamic

open LeanLoad.Parse.Bytes
open LeanLoad.Spec.Dynamic

/-- Parse a single `Elf64_Dyn` at the current cursor. -/
def parseEntry : Parser Dyn64 := do
  let d_tag ← u64le
  let d_un  ← u64le
  return { d_tag, d_un }

/-- Read entries up to and including `DT_NULL`, or until `limit` bytes
    have been consumed. `limit` is `(offset + p_filesz)` for the
    enclosing `PT_DYNAMIC` segment. -/
private partial def collect (limit : Nat) (acc : Array Dyn64) : Parser (Array Dyn64) := do
  let cur ← pos
  if cur >= limit then
    return acc
  let e ← parseEntry
  let acc := acc.push e
  if e.d_tag == DT_NULL then
    return acc
  collect limit acc

/-- Parse the `.dynamic` array. `offset` is the file offset (typically
    `p_offset` of the `PT_DYNAMIC` program header) and `bytes` is its
    `p_filesz`. -/
def parseTable (offset bytes : Nat) : Parser (Array Dyn64) := do
  seek offset
  collect (offset + bytes) (Array.mkEmpty 16)

end LeanLoad.Parse.Dynamic

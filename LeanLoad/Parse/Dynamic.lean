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
    have been consumed. `fuel` bounds the recursion depth — the
    caller seeds it with the byte count, which dominates the
    one-entry-per-iteration loop (each entry is `entrySize` bytes).
    With this, no `partial def` is needed. -/
private def collect (fuel : Nat) (limit : Nat) (acc : Array Dyn64) : Parser (Array Dyn64) := do
  match fuel with
  | 0 => return acc
  | fuel + 1 =>
    let cur ← pos
    if cur >= limit then
      return acc
    let e ← parseEntry
    let acc := acc.push e
    if e.d_tag == DT_NULL then
      return acc
    collect fuel limit acc

/-- Parse the `.dynamic` array. `offset` is the file offset (typically
    `p_offset` of the `PT_DYNAMIC` program header) and `bytes` is its
    `p_filesz`. Fuel = `bytes`: with `entrySize ≥ 1` byte per
    iteration, this overcounts but is sound. -/
def parseTable (offset bytes : Nat) : Parser (Array Dyn64) := do
  seek offset
  collect bytes (offset + bytes) (Array.mkEmpty 16)

-- ============================================================================
-- Lookup helpers over a parsed `.dynamic` table. Used by callers
-- (`Parse.File`, `Discover`) to extract individual entries by tag.
-- ============================================================================

/-- Find the first entry with the given tag. -/
def find? (tab : Array Dyn64) (tag : UInt64) : Option Dyn64 :=
  tab.find? (·.d_tag == tag)

/-- All entries matching a tag (e.g. all `DT_NEEDED`). -/
def findAll (tab : Array Dyn64) (tag : UInt64) : Array Dyn64 :=
  tab.filter (·.d_tag == tag)

section Example
-- Synthetic .dynamic with three NEEDED entries plus singletons.
private def tab : Array Dyn64 := #[
  { d_tag := DT_NEEDED, d_un := 0x10 },
  { d_tag := DT_RUNPATH, d_un := 0x20 },
  { d_tag := DT_NEEDED, d_un := 0x30 },
  { d_tag := DT_NEEDED, d_un := 0x40 },
  { d_tag := DT_NULL,   d_un := 0 } ]

#guard (find? tab DT_NEEDED).map (·.d_un)  = some 0x10   -- first match wins
#guard (find? tab DT_RUNPATH).map (·.d_un) = some 0x20
#guard  find? tab DT_HASH                  = none         -- absent

-- All three NEEDED entries, in declared order.
#guard (findAll tab DT_NEEDED).map (·.d_un) = #[0x10, 0x30, 0x40]
#guard (findAll tab DT_HASH).size           = 0
end Example

end LeanLoad.Parse.Dynamic

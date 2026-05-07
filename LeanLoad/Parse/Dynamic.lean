/-
The `.dynamic` array — variable-length parser.

Spec: gabi 08 (`third_party/gabi/docsrc/elf/08-dynamic.rst`) § Dynamic
Section.

The array is `DT_NULL`-terminated, so it can't use the generic
`Bytes.decodeArray` (fixed-count). Hence this dedicated file. The
`RawDyn` type and `DT_*` tag constants live in `Parse/Structs.lean`.
-/

import LeanLoad.Parse.Structs

namespace LeanLoad.Parse.Dynamic

open LeanLoad.Parse
open LeanLoad.Parse.Bytes

/-- Read entries up to and including `DT_NULL`, or until `limit` bytes
    have been consumed. -/
private def collect (fuel : Nat) (limit : Nat) (acc : Array RawDyn) :
    Parser (Array RawDyn) := do
  match fuel with
  | 0 => return acc
  | fuel + 1 =>
    let cur ← pos
    if cur >= limit then
      return acc
    let e ← BytesDecode.decode
    let acc := acc.push e
    if e.d_tag == DT_NULL then
      return acc
    collect fuel limit acc

/-- Parse the `.dynamic` array. `offset` is the file offset (typically
    `p_offset` of the `PT_DYNAMIC` program header) and `bytes` is its
    `p_filesz`. -/
def parseTable (offset bytes : Nat) : Parser (Array RawDyn) := do
  seek offset
  collect bytes (offset + bytes) (Array.mkEmpty 16)

/-- Find the first entry with the given tag. -/
def find? (tab : Array RawDyn) (tag : UInt64) : Option RawDyn :=
  tab.find? (·.d_tag == tag)

/-- All entries matching a tag (e.g. all `DT_NEEDED`). -/
def findAll (tab : Array RawDyn) (tag : UInt64) : Array RawDyn :=
  tab.filter (·.d_tag == tag)

section Example
private def tab : Array RawDyn := #[
  { d_tag := DT_NEEDED, d_un := 0x10 },
  { d_tag := DT_RUNPATH, d_un := 0x20 },
  { d_tag := DT_NEEDED, d_un := 0x30 },
  { d_tag := DT_NEEDED, d_un := 0x40 },
  { d_tag := DT_NULL,   d_un := 0 } ]

#guard (find? tab DT_NEEDED).map (·.d_un)  = some 0x10
#guard (find? tab DT_RUNPATH).map (·.d_un) = some 0x20
#guard  find? tab DT_HASH                  = none

#guard (findAll tab DT_NEEDED).map (·.d_un) = #[0x10, 0x30, 0x40]
#guard (findAll tab DT_HASH).size           = 0
end Example

end LeanLoad.Parse.Dynamic

/-
The `.dynamic` array — variable-length parser + lookup helpers.

Spec: gabi 08 (`third_party/gabi/docsrc/elf/08-dynamic.rst`) § Dynamic
Section.

The array is `DT_NULL`-terminated, so it can't use the generic
`decodeArray` (fixed-count) — hence this dedicated file. The
`RawDyn` type and `DT_*` tag constants live in `Parse/Structs.lean`;
the parser and the by-tag lookups live here.
-/

import LeanLoad.Parse.Structs

namespace LeanLoad.Parse.Dynamic

open LeanLoad.Parse

/-- Read entries up to and including `DT_NULL`, or until `limit`
    bytes have been consumed. -/
private def collect (fuel : Nat) (limit : Nat) (acc : Array RawDyn) :
    Parser (Array RawDyn) := do
  match fuel with
  | 0 => return acc
  | fuel + 1 =>
    let cur ← cursor
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

-- ============================================================================
-- Lookup helpers over a parsed `.dynamic` array.
-- ============================================================================

/-- First entry with the given tag. -/
def find? (tab : Array RawDyn) (tag : UInt64) : Option RawDyn :=
  tab.find? (·.d_tag == tag)

/-- All entries matching a tag (e.g. all `DT_NEEDED`). -/
def findAll (tab : Array RawDyn) (tag : UInt64) : Array RawDyn :=
  tab.filter (·.d_tag == tag)

/-- Value of the first entry with `tag`, or `none`. -/
def val? (tab : Array RawDyn) (tag : UInt64) : Option UInt64 :=
  (find? tab tag).map (·.d_un)

/-- Values of two tags as a pair, `none` if either is absent.
    Used to read `(addr, size)`-style sized sections like
    `(DT_RELA, DT_RELASZ)` in one shot. -/
def pair? (tab : Array RawDyn) (tagA tagB : UInt64) : Option (UInt64 × UInt64) := do
  let a ← val? tab tagA
  let b ← val? tab tagB
  return (a, b)

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

#guard val? tab DT_NEEDED          = some 0x10
#guard pair? tab DT_NEEDED DT_NULL = some (0x10, 0)
#guard pair? tab DT_NEEDED DT_HASH = none
end Example

end LeanLoad.Parse.Dynamic

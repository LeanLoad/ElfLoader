/-
gabi 08 § Dynamic Section — `Elf64_Dyn` entry, plus the `.dynamic`
array parser and by-tag lookups.

Spec: gabi 08 (`third_party/gabi/docsrc/elf/08-dynamic.rst`).

`DynTag` lives in `Parse/Dyntab/Fields.lean`; this file owns the raw
entry shape and the `DT_NULL`-terminated table parser.

The `.dynamic` array is `DT_NULL`-terminated, so it can't use the
generic `decodeArray` (fixed-count) — `RawDyntab.parse` below is
the dedicated parser. It rejects unterminated or non-entry-sized tables
instead of silently treating malformed tails as absent dynamic state.
`RawDyntab.findAll / val?` are post-parse lookups over the resulting
`RawDyntab`. The one-shot projection into a record of dynamic-content
pointers lives in `Parse/Dyntab/Info.lean`.
-/

import LeanLoad.Parse.Decode
import LeanLoad.Parse.Deriving
import LeanLoad.Parse.Address
import LeanLoad.Parse.Dyntab.Fields

namespace LeanLoad.Parse

/-- One entry of the `.dynamic` array. `d_un` holds either `d_val`
    (an integer) or `d_ptr` (a virtual address); the interpretation
    is controlled by `d_tag`. -/
structure RawDyn where
  d_tag : DynTag
  d_un  : UInt64
  deriving Repr, Inhabited, BytesDecode

/-- Size of one `Elf64_Dyn` on disk: 8+8 = 16. -/
def RawDynSize : Nat := 16

/-- Parsed `.dynamic` array — `DT_NULL`-terminated sequence of
    `RawDyn` entries. Lookups via `RawDyntab.findAll / val?`;
    one-shot projection into `DynInfo` via `DynInfo.ofTable`. -/
abbrev RawDyntab := Array RawDyn

namespace RawDyntab

/-- Read entries up to and including `DT_NULL`; fail if the entry budget is
    exhausted first. gABI 08 § Dynamic Section requires a terminating
    `DT_NULL` entry. -/
private def collect (fuel : Nat) (acc : RawDyntab) : Parser RawDyntab := do
  match fuel with
  | 0 => throw "dynamic table missing DT_NULL terminator (gabi 08 § Dynamic Section)"
  | fuel + 1 =>
    let e : RawDyn ← BytesDecode.decode
    let acc := acc.push e
    if e.d_tag == .null then
     return acc
    collect fuel acc

/-- Parse the `.dynamic` array from the current cursor. `bytes` is the
    section byte length, typically the `p_filesz` of the `PT_DYNAMIC`
    program header. -/
def parse (bytes : ByteSize) : Parser RawDyntab := do
  let n := bytes.toNat
  if n == 0 then
    throw "dynamic table has zero byte size; expected at least one DT_NULL entry"
  else if n % RawDynSize != 0 then
    throw s!"dynamic table byte size {n} is not a multiple of {RawDynSize}"
  else
    let entries := n / RawDynSize
    collect entries (Array.mkEmpty entries)

/-- All entries matching a tag (e.g. all `DT_NEEDED`). -/
def findAll (tab : RawDyntab) (tag : DynTag) : RawDyntab :=
  tab.filter (·.d_tag == tag)

/-- Value of the first entry with `tag`, or `none`. -/
def val? (tab : RawDyntab) (tag : DynTag) : Option UInt64 :=
  (tab.find? (·.d_tag == tag)).map (·.d_un)

end RawDyntab

end LeanLoad.Parse

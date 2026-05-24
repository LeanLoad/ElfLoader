import LeanLoad.Parse.Decode.Decodable
import LeanLoad.Parse.Decode.Deriving
import LeanLoad.Parse.Basic
import LeanLoad.Parse.DynMap.Fields

/-!
Raw `.dynamic` decoding.

`RawEntry` / `RawDyntab` are the implementation layer for gABI `Elf64_Dyn`
records. `DynMap.Basic` interprets them into parse-stage dynamic facts.

Spec: gabi 08 (`third_party/gabi/docsrc/elf/08-dynamic.rst`).
-/

namespace LeanLoad.Parse

/-- One raw `Elf64_Dyn` entry. `d_un` holds either `d_val` or `d_ptr`;
    `DynMap` interprets it according to `d_tag`. -/
structure RawEntry where
  d_tag : DynTag
  d_un  : UInt64
  deriving Repr, Inhabited, Decodable

#guard (Decodable.byteSize (α := RawEntry)).toNat = 16  -- gabi 08 § Dynamic Section: `Elf64_Dyn`

/-- Raw `.dynamic` array — a `DT_NULL`-terminated sequence of `Elf64_Dyn` entries. -/
abbrev RawDyntab := Array RawEntry

namespace RawDyntab

/-- Read entries up to and including `DT_NULL`; fail if the entry budget is
    exhausted first. gABI 08 § Dynamic Section requires a terminating
    `DT_NULL` entry. -/
private def collect (fuel : Nat) (acc : RawDyntab) : Decoder RawDyntab := do
  match fuel with
  | 0 => throw "dynamic table missing DT_NULL terminator (gabi 08 § Dynamic Section)"
  | fuel + 1 =>
      let e : RawEntry ← Decodable.decoder
      let acc := acc.push e
      if e.d_tag == .null then
        return acc
      collect fuel acc

/-- Decoder for the `.dynamic` array from the current cursor. `bytes` is the
    section byte length, typically the `p_filesz` of the `PT_DYNAMIC`
    program header. -/
def decoder (bytes : ByteSize) : Decoder RawDyntab := do
  let n := bytes.toNat
  let entrySize := (Decodable.byteSize (α := RawEntry)).toNat
  if n == 0 then
    -- gABI 08 § Dynamic Section: `_DYNAMIC` ends with a mandatory `DT_NULL`.
    throw "dynamic table has zero byte size; expected at least one DT_NULL entry"
  else if n % entrySize != 0 then
    throw s!"dynamic table byte size {n} is not a multiple of {entrySize}"
  else
    let entries := n / entrySize
    collect entries (Array.mkEmpty entries)

/-- All raw entries matching a tag (e.g. all `DT_NEEDED`). -/
def findAll (tab : RawDyntab) (tag : DynTag) : RawDyntab :=
  tab.filter (·.d_tag == tag)

/-- Value of the first entry with `tag`, or `none`. -/
def val? (tab : RawDyntab) (tag : DynTag) : Option UInt64 :=
  (tab.find? (·.d_tag == tag)).map (·.d_un)

/-- Value of a tag that must appear at most once. Repeated singleton tags are
    rejected here so downstream parsing does not depend on "first wins" order. -/
def single? (tab : RawDyntab) (tag : DynTag) : Except String (Option UInt64) :=
  let vals := (findAll tab tag).map (·.d_un)
  if vals.size == 0 then
    .ok none
  else if vals.size == 1 then
    .ok (some (vals[0]?.getD 0))
  else
    .error s!"parse: duplicate {tag.label} entries ({vals.size})"

/-- Pair an ELF-address tag with its size tag. Half-present pairs are rejected;
    gABI 08's dynamic locators are only meaningful as a complete range. -/
def rawRange? (tab : RawDyntab) (addrTag sizeTag : DynTag) :
    Except String (Option EaddrRange) := do
  let addr ← single? tab addrTag
  let size ← single? tab sizeTag
  match addr, size with
  | none, none       => .ok none
  | some v, some len => .ok (some { start := ⟨v⟩, size := ⟨len⟩ })
  | some _, none     => .error s!"parse: {addrTag.label} present without {sizeTag.label}"
  | none, some _     => .error s!"parse: {sizeTag.label} present without {addrTag.label}"

end RawDyntab

end LeanLoad.Parse

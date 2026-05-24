/-
gabi 08 § Dynamic Section — `Elf64_Dyn` entry, plus the `.dynamic`
array decoder and by-tag lookups.

Spec: gabi 08 (`third_party/gabi/docsrc/elf/08-dynamic.rst`).

`DynTag` lives in `Parse/Dynamic/Dyntab/Fields.lean`; this file owns the entry
shape and the `DT_NULL`-terminated table decoder.

The `.dynamic` array is `DT_NULL`-terminated, so it can't use the
generic `Decoder.array` (fixed-count) — `Dyntab.decode` below is
the dedicated decoder. It rejects unterminated or non-entry-sized tables
instead of silently treating malformed tails as absent dynamic state.
`Dyntab.findAll / val?` are post-parse lookups over the resulting table;
small accessors project the dynamic-content ranges that drive later reads.
-/

import LeanLoad.Parse.Decode.Decodable
import LeanLoad.Parse.Decode.Deriving
import LeanLoad.Parse.Address
import LeanLoad.Parse.Dynamic.Dyntab.Fields
import LeanLoad.Parse.Dynamic.Symbol.Raw
import LeanLoad.Parse.Dynamic.Reloc.Raw

namespace LeanLoad.Parse

namespace Dyntab

/-- One entry of the `.dynamic` array. `d_un` holds either `d_val`
    (an integer) or `d_ptr` (a ELF address); the interpretation
    is controlled by `d_tag`. -/
structure Entry where
  d_tag : DynTag
  d_un  : UInt64
  deriving Repr, Inhabited, Decodable

/-- Size of one `Elf64_Dyn` on disk: 8+8 = 16. -/
def EntrySize : Nat := 16

end Dyntab

/-- Parsed `.dynamic` array — `DT_NULL`-terminated sequence of
    `Dyntab.Entry` entries. Lookups via `Dyntab.findAll / val?`; typed
    accessors project the content ranges and string offsets. -/
abbrev Dyntab := Array Dyntab.Entry

namespace Dyntab

/-- Read entries up to and including `DT_NULL`; fail if the entry budget is
    exhausted first. gABI 08 § Dynamic Section requires a terminating
    `DT_NULL` entry. -/
private def collect (fuel : Nat) (acc : Dyntab) : Decoder Dyntab := do
  match fuel with
  | 0 => throw "dynamic table missing DT_NULL terminator (gabi 08 § Dynamic Section)"
  | fuel + 1 =>
    let e : Entry ← Decodable.decoder
    let acc := acc.push e
    if e.d_tag == .null then
     return acc
    collect fuel acc

/-- Decode the `.dynamic` array from the current cursor. `bytes` is the
    section byte length, typically the `p_filesz` of the `PT_DYNAMIC`
    program header. -/
def decode (bytes : ByteSize) : Decoder Dyntab := do
  let n := bytes.toNat
  if n == 0 then
    throw "dynamic table has zero byte size; expected at least one DT_NULL entry"
  else if n % EntrySize != 0 then
    throw s!"dynamic table byte size {n} is not a multiple of {EntrySize}"
  else
    let entries := n / EntrySize
    collect entries (Array.mkEmpty entries)

/-- All entries matching a tag (e.g. all `DT_NEEDED`). -/
def findAll (tab : Dyntab) (tag : DynTag) : Dyntab :=
  tab.filter (·.d_tag == tag)

/-- Value of the first entry with `tag`, or `none`. -/
def val? (tab : Dyntab) (tag : DynTag) : Option UInt64 :=
  (tab.find? (·.d_tag == tag)).map (·.d_un)

/-- Value of a tag that must appear at most once. Repeated singleton tags are
    rejected here so downstream parsing does not depend on "first wins" order. -/
private def single? (tab : Dyntab) (tag : DynTag) : Except String (Option UInt64) :=
  let vals := (findAll tab tag).map (·.d_un)
  if vals.size == 0 then
    .ok none
  else if vals.size == 1 then
    .ok (some (vals[0]?.getD 0))
  else
    .error s!"parse: duplicate {tag.label} entries ({vals.size})"

/-- Pair an ELF-address tag with its size tag. Half-present pairs are
    rejected; gABI 08's dynamic locators are only meaningful as a complete
    range. -/
private def rawRange? (tab : Dyntab) (addrTag sizeTag : DynTag) :
    Except String (Option EaddrRange) := do
  let addr ← single? tab addrTag
  let size ← single? tab sizeTag
  match addr, size with
  | none, none       => .ok none
  | some v, some len => .ok (some { start := ⟨v⟩, size := ⟨len⟩ })
  | some _, none     => .error s!"parse: {addrTag.label} present without {sizeTag.label}"
  | none, some _     => .error s!"parse: {sizeTag.label} present without {addrTag.label}"

/-- Validate a present `DT_*ENT`-style byte-size tag against the entry size
    consumed by the decoder's fixed Elf64 readers. -/
private def validateEntrySize (tag : DynTag) (expected : Nat) (value : Option UInt64) :
    Except String Unit :=
  match value with
  | none => .ok ()
  | some actual =>
      if actual.toNat == expected then
        .ok ()
      else
        .error s!"parse: {tag.label}={actual.toNat}, expected {expected}"

/-- Require an already-read entry-size tag when its table tag is present. -/
private def requireEntrySize (tableTag entryTag : DynTag)
    (expected : Nat) (tablePresent : Bool) (value : Option UInt64) :
    Except String Unit := do
  if tablePresent && value.isNone then
    .error s!"parse: {tableTag.label} present without {entryTag.label}"
  else
    validateEntrySize entryTag expected value

/-- All `DT_NEEDED` strtab byte-offsets, in dynamic-array order. -/
def needed (tab : Dyntab) : Array StrtabOff :=
  (findAll tab .needed).map (⟨·.d_un⟩)

/-- `DT_SONAME` strtab byte-offset, if present. -/
def soname? (tab : Dyntab) : Except String (Option StrtabOff) :=
  (single? tab .soname).map (·.map StrtabOff.mk)

/-- `DT_RUNPATH` strtab byte-offset, if present. `DT_RPATH` is intentionally not
    consulted (deprecated by gabi 08; `Discover/IO.lean` refuses it too). -/
def runpath? (tab : Dyntab) : Except String (Option StrtabOff) :=
  (single? tab .runpath).map (·.map StrtabOff.mk)

/-- `DT_STRTAB/DT_STRSZ` ELF-address range, when present. -/
def strtab? (tab : Dyntab) : Except String (Option EaddrRange) :=
  rawRange? tab .strtab .strsz

/-- `DT_SYMTAB` ELF address, when present. `DT_SYMENT` is required because the
    fixed-width symbol decoder assumes Elf64_Sym entries. -/
def symtab? (tab : Dyntab) : Except String (Option Eaddr) := do
  let symtabRaw ← single? tab .symtab
  let symentRaw ← single? tab .syment
  requireEntrySize .symtab .syment RawSymSize symtabRaw.isSome symentRaw
  return symtabRaw.map Eaddr.mk

/-- `DT_HASH` ELF address, when present. Its `nchain` field gives the dynamic
    symbol count used by `Dynamic` when `DT_SYMTAB` is also present. -/
def hash? (tab : Dyntab) : Except String (Option Eaddr) :=
  (single? tab .hash).map (·.map Eaddr.mk)

/-- `DT_RELA/DT_RELASZ` ELF-address range, when present. -/
def rela? (tab : Dyntab) : Except String (Option EaddrRange) := do
  let loc ← rawRange? tab .rela .relasz
  let relaentRaw ← single? tab .relaent
  requireEntrySize .rela .relaent RawRelaSize loc.isSome relaentRaw
  return loc

/-- `DT_JMPREL/DT_PLTRELSZ` ELF-address range, when present. -/
def jmprel? (tab : Dyntab) : Except String (Option EaddrRange) :=
  rawRange? tab .jmprel .pltrelsz

/-- `DT_PLTREL`, when present. gABI 08 says it describes the relocation entry
    encoding used by `DT_JMPREL`. -/
def pltrel? (tab : Dyntab) : Except String (Option PltRelKind) := do
  match ← single? tab .pltrel with
  | none     => return none
  | some raw => PltRelKind.ofRaw raw |>.map some

/-- `DT_INIT_ARRAY/DT_INIT_ARRAYSZ` ELF-address range, when present. -/
def initArr? (tab : Dyntab) : Except String (Option EaddrRange) := do
  rawRange? tab .initArray .initArraySz

/-- `DT_FINI_ARRAY/DT_FINI_ARRAYSZ` ELF-address range, when present. -/
def finiArr? (tab : Dyntab) : Except String (Option EaddrRange) := do
  rawRange? tab .finiArray .finiArraySz

end Dyntab

end LeanLoad.Parse

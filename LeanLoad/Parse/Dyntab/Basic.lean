/-
gabi 08 § Dynamic Section — `Elf64_Dyn` entry, plus the `.dynamic`
array parser and by-tag lookups.

Spec: gabi 08 (`third_party/gabi/docsrc/elf/08-dynamic.rst`).

`DynTag` lives in `Parse/Dyntab/Fields.lean`; this file owns the entry
shape and the `DT_NULL`-terminated table parser.

The `.dynamic` array is `DT_NULL`-terminated, so it can't use the
generic `decodeArray` (fixed-count) — `Dyntab.parse` below is
the dedicated parser. It rejects unterminated or non-entry-sized tables
instead of silently treating malformed tails as absent dynamic state.
`Dyntab.findAll / val?` are post-parse lookups over the resulting table;
small accessors project the dynamic-content spans that drive later reads.
-/

import LeanLoad.Parse.Decode
import LeanLoad.Parse.Deriving
import LeanLoad.Parse.Address
import LeanLoad.Parse.Dyntab.Fields
import LeanLoad.Parse.Symbol.Raw
import LeanLoad.Parse.Reloc.Raw

namespace LeanLoad.Parse

namespace Dyntab

/-- One entry of the `.dynamic` array. `d_un` holds either `d_val`
    (an integer) or `d_ptr` (a virtual address); the interpretation
    is controlled by `d_tag`. -/
structure Entry where
  d_tag : DynTag
  d_un  : UInt64
  deriving Repr, Inhabited, BytesDecode

/-- Size of one `Elf64_Dyn` on disk: 8+8 = 16. -/
def EntrySize : Nat := 16

end Dyntab

/-- Parsed `.dynamic` array — `DT_NULL`-terminated sequence of
    `Dyntab.Entry` entries. Lookups via `Dyntab.findAll / val?`; typed
    accessors project the content spans and string offsets. -/
abbrev Dyntab := Array Dyntab.Entry

namespace Dyntab

/-- Read entries up to and including `DT_NULL`; fail if the entry budget is
    exhausted first. gABI 08 § Dynamic Section requires a terminating
    `DT_NULL` entry. -/
private def collect (fuel : Nat) (acc : Dyntab) : Parser Dyntab := do
  match fuel with
  | 0 => throw "dynamic table missing DT_NULL terminator (gabi 08 § Dynamic Section)"
  | fuel + 1 =>
    let e : Entry ← BytesDecode.decode
    let acc := acc.push e
    if e.d_tag == .null then
     return acc
    collect fuel acc

/-- Parse the `.dynamic` array from the current cursor. `bytes` is the
    section byte length, typically the `p_filesz` of the `PT_DYNAMIC`
    program header. -/
def parse (bytes : ByteSize) : Parser Dyntab := do
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
private def single? (tab : Dyntab) (label : String) (tag : DynTag) :
    Except String (Option UInt64) :=
  let vals := (findAll tab tag).map (·.d_un)
  if vals.size == 0 then
    .ok none
  else if vals.size == 1 then
    .ok (some (vals[0]?.getD 0))
  else
    .error s!"parse: duplicate {label} entries ({vals.size})"

/-- Pair a virtual-address tag with its size tag. Half-present pairs are
    rejected; gABI 08's dynamic locators are only meaningful as a complete
    span. -/
private def span? (label addrLabel sizeLabel : String)
    (addr size : Option UInt64) : Except String (Option VaddrSpan) :=
  match addr, size with
  | none, none       => .ok none
  | some v, some len => .ok (some { start := ⟨v⟩, size := ⟨len⟩ })
  | some _, none     => .error s!"parse: {label}: {addrLabel} present without {sizeLabel}"
  | none, some _     => .error s!"parse: {label}: {sizeLabel} present without {addrLabel}"

/-- Validate a present `DT_*ENT`-style byte-size tag against the entry size
    consumed by the parser's fixed Elf64 readers. -/
private def validateEntrySize (label : String) (expected : Nat) (value : Option UInt64) :
    Except String Unit :=
  match value with
  | none => .ok ()
  | some actual =>
      if actual.toNat == expected then
        .ok ()
      else
        .error s!"parse: {label}={actual.toNat}, expected {expected}"

/-- Require an already-read entry-size tag when its table tag is present. -/
private def requireEntrySize (tableLabel entryLabel : String)
    (expected : Nat) (tablePresent : Bool) (value : Option UInt64) :
    Except String Unit := do
  if tablePresent && value.isNone then
    .error s!"parse: {tableLabel} present without {entryLabel}"
  else
    validateEntrySize entryLabel expected value

/-- All `DT_NEEDED` strtab byte-offsets, in dynamic-array order. -/
def needed (tab : Dyntab) : Array StrtabOff :=
  (findAll tab .needed).map (⟨·.d_un⟩)

/-- `DT_SONAME` strtab byte-offset, if present. -/
def soname? (tab : Dyntab) : Except String (Option StrtabOff) := do
  let sonameRaw ← single? tab "DT_SONAME" .soname
  return sonameRaw.map StrtabOff.mk

/-- `DT_RUNPATH` strtab byte-offset, if present. `DT_RPATH` is intentionally not
    consulted (deprecated by gabi 08; `Discover/IO.lean` refuses it too). -/
def runpath? (tab : Dyntab) : Except String (Option StrtabOff) := do
  let runpathRaw ← single? tab "DT_RUNPATH" .runpath
  return runpathRaw.map StrtabOff.mk

/-- `DT_STRTAB/DT_STRSZ` virtual span, when present. String references require
    a complete string-table span. -/
def strtab? (tab : Dyntab) : Except String (Option VaddrSpan) := do
  let loc ← span? "DT_STRTAB/DT_STRSZ" "DT_STRTAB" "DT_STRSZ"
    (← single? tab "DT_STRTAB" .strtab) (← single? tab "DT_STRSZ" .strsz)
  let sonameRaw ← single? tab "DT_SONAME" .soname
  let runpathRaw ← single? tab "DT_RUNPATH" .runpath
  if loc.isNone && (needed tab).size != 0 || loc.isNone && sonameRaw.isSome ||
      loc.isNone && runpathRaw.isSome then
    .error "parse: dynamic string references present without DT_STRTAB/DT_STRSZ"
  else
    return loc

/-- `(DT_SYMTAB vaddr, DT_HASH vaddr)`, when present. `DT_HASH.nchain` is the
    dynamic-symbol count; LeanLoad requires it with `DT_SYMTAB`. -/
def symtabHash? (tab : Dyntab) : Except String (Option (Vaddr × Vaddr)) := do
  let symtabRaw ← single? tab "DT_SYMTAB" .symtab
  let symentRaw ← single? tab "DT_SYMENT" .syment
  let hashRaw ← single? tab "DT_HASH" .hash
  requireEntrySize "DT_SYMTAB" "DT_SYMENT" RawSymSize symtabRaw.isSome symentRaw
  match symtabRaw, hashRaw with
  | none, none       => return none
  | some sym, some h => return some (⟨sym⟩, ⟨h⟩)
  | some _, none     => .error "parse: DT_SYMTAB present without DT_HASH"
  | none, some _     => .error "parse: DT_HASH present without DT_SYMTAB"

/-- `DT_RELA/DT_RELASZ` virtual span, when present. -/
def rela? (tab : Dyntab) : Except String (Option VaddrSpan) := do
  let loc ← span? "DT_RELA/DT_RELASZ" "DT_RELA" "DT_RELASZ"
    (← single? tab "DT_RELA" .rela) (← single? tab "DT_RELASZ" .relasz)
  let relaentRaw ← single? tab "DT_RELAENT" .relaent
  requireEntrySize "DT_RELA" "DT_RELAENT" RawRelaSize loc.isSome relaentRaw
  return loc

/-- `DT_JMPREL/DT_PLTRELSZ` virtual span, when present. LeanLoad only
    accepts PLT relocations encoded as Elf64_Rela (`DT_PLTREL = DT_RELA`). -/
def jmprel? (tab : Dyntab) : Except String (Option VaddrSpan) := do
  let loc ← span? "DT_JMPREL/DT_PLTRELSZ" "DT_JMPREL" "DT_PLTRELSZ"
    (← single? tab "DT_JMPREL" .jmprel) (← single? tab "DT_PLTRELSZ" .pltrelsz)
  let pltrelRaw ← single? tab "DT_PLTREL" .pltrel
  match pltrelRaw with
  | none =>
      if loc.isSome then
        .error "parse: DT_JMPREL present without DT_PLTREL"
      else
        return loc
  | some actual =>
      match PltRelKind.ofRaw actual with
      | .ok .rela => return loc
      | .ok .rel  => .error "parse: DT_PLTREL=DT_REL, expected DT_RELA"
      | .error e  => .error e

/-- `DT_INIT_ARRAY/DT_INIT_ARRAYSZ` virtual span, when present. -/
def initArr? (tab : Dyntab) : Except String (Option VaddrSpan) := do
  span? "DT_INIT_ARRAY/DT_INIT_ARRAYSZ" "DT_INIT_ARRAY"
    "DT_INIT_ARRAYSZ" (← single? tab "DT_INIT_ARRAY" .initArray)
    (← single? tab "DT_INIT_ARRAYSZ" .initArraySz)

/-- `DT_FINI_ARRAY/DT_FINI_ARRAYSZ` virtual span, when present. -/
def finiArr? (tab : Dyntab) : Except String (Option VaddrSpan) := do
  span? "DT_FINI_ARRAY/DT_FINI_ARRAYSZ" "DT_FINI_ARRAY"
    "DT_FINI_ARRAYSZ" (← single? tab "DT_FINI_ARRAY" .finiArray)
    (← single? tab "DT_FINI_ARRAYSZ" .finiArraySz)

end Dyntab

end LeanLoad.Parse

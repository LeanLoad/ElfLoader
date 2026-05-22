/-
One-shot projection of `RawDyntab` — `Parse.parse`'s dynamic-table layer.

Every dynamic-content locating tag this loader consults is resolved here,
into a single record of `(vaddr [× size])` pointers. After successful
`DynInfo.ofTable`, layer 3 reads `DynInfo` fields directly and the raw
`.dynamic` array is no longer referenced.

The `(DT_X, DT_XSZ)` pairing lives here, not in `parse`. That
isolates "which tag means what" from "where in the file are those
bytes" — `parse` becomes a straight `Ehdr → Array RawPhdr →
RawDyntab → DynInfo → layer-3 reads` pipeline.

DynInfo is parse-internal: it is not exposed on `Elf` (the raw
`.dynamic` array is not carried past checked parse). Projection is strict:
duplicate singleton tags and half-present `(DT_X, DT_XSZ)` locators are
parse errors, not `none`. Each field's resolved value either flows directly
into a checked `Elf` field or drives a layer-3 read.

The raw `d_un : UInt64` values are wrapped into three semantic kinds at
this boundary:

  • **strtab byte-offset** (`needed`, `soname`, `runpath`) — index
    into the parsed `.dynstr` buffer; `RawStrtab.lookup` consumes these
    directly. *Not* a file offset, *not* a vaddr.

  • **vaddr** (`strtab.1`, `symtab`, `hash`, `rela.1`, `jmprel.1`,
    `initArr.1`, `finiArr.1`) — virtual address as recorded in
    `.dynamic`; the checked `LoadMap` translates it to a file offset at
    layer-3 read time.

  • **byte size** (`strtab.2`, `rela.2`, `jmprel.2`, `initArr.2`,
    `finiArr.2`) — content length in bytes; entry count derives from
    `size / entrySize`.

`DT_RPATH` is **intentionally not honoured** (gabi 08 deprecates it;
`Discover/IO.lean` and `Runtime.c` refuse to honour it too). `runpath`
is set from `DT_RUNPATH` alone — a DT_RPATH-only object yields
`runpath = none`.
-/

import LeanLoad.Parse.Dyntab.Raw
import LeanLoad.Parse.Address

namespace LeanLoad.Parse

/-- Projection of a parsed `.dynamic` array. Each field holds the
    resolved, semantically typed value (or pair) for one
    dynamic-content locating tag. -/
structure DynInfo where
  /-- All `DT_NEEDED` strtab byte-offsets, in dynamic-array order.
      `RawStrtab.lookup strtab offset` resolves each to a name. -/
  needed  : Array StrtabOff
  /-- `DT_SONAME` strtab byte-offset, if present. -/
  soname  : Option StrtabOff
  /-- `DT_RUNPATH` strtab byte-offset, if present. `DT_RPATH` is
      intentionally **not** consulted (deprecated by gabi 08;
      `Discover/IO.lean` refuses it too). -/
  runpath : Option StrtabOff
  /-- `(DT_STRTAB vaddr, DT_STRSZ byte-size)`. -/
  strtab  : Option (Vaddr × ByteSize)
  /-- `DT_SYMTAB` vaddr. Entry count comes from `DT_HASH.nchain`,
      not from any `DT_*SZ` tag. -/
  symtab  : Option Vaddr
  /-- `DT_HASH` vaddr. First 8 bytes are a `RawSysVHash` header; only
      `nchain` is read (sizes the symtab). -/
  hash    : Option Vaddr
  /-- `(DT_RELA vaddr, DT_RELASZ byte-size)`. -/
  rela    : Option (Vaddr × ByteSize)
  /-- `(DT_JMPREL vaddr, DT_PLTRELSZ byte-size)`. -/
  jmprel  : Option (Vaddr × ByteSize)
  /-- `(DT_INIT_ARRAY vaddr, DT_INIT_ARRAYSZ byte-size)`. -/
  initArr : Option (Vaddr × ByteSize)
  /-- `(DT_FINI_ARRAY vaddr, DT_FINI_ARRAYSZ byte-size)`. -/
  finiArr : Option (Vaddr × ByteSize)
  deriving Repr, Inhabited

namespace DynInfo

/-- Value of a tag that must appear at most once. Repeated singleton tags are
    rejected here so downstream parsing does not depend on "first wins" order. -/
private def single? (tab : RawDyntab) (label : String) (tag : DynTag) :
    Except String (Option UInt64) :=
  let vals := (RawDyntab.findAll tab tag).map (·.d_un)
  if vals.size == 0 then
    .ok none
  else if vals.size == 1 then
    .ok (some (vals[0]?.getD 0))
  else
    .error s!"parse: duplicate {label} entries ({vals.size})"

/-- Pair an address-like tag with its size tag. Half-present pairs are rejected;
    gABI 08's dynamic locators are only meaningful as a complete pair. -/
private def pair? (tab : RawDyntab) (label addrLabel sizeLabel : String)
    (addrTag sizeTag : DynTag) : Except String (Option (Vaddr × ByteSize)) := do
  let addr ← single? tab addrLabel addrTag
  let size ← single? tab sizeLabel sizeTag
  match addr, size with
  | none, none       => .ok none
  | some v, some len => .ok (some (⟨v⟩, ⟨len⟩))
  | some _, none     => .error s!"parse: {label}: {addrLabel} present without {sizeLabel}"
  | none, some _     => .error s!"parse: {label}: {sizeLabel} present without {addrLabel}"

/-- Resolve every dynamic-content locating tag in one pass. Absent tags
    become `none`; malformed partial locators and duplicate singleton tags are
    errors. `DT_RPATH` is **not** consulted — see `runpath`'s docstring.
    After this, `parse` no longer touches the raw array.

    Each `d_un` value is wrapped into its semantic type (`StrtabOff`, `Vaddr`,
    or `ByteSize`) at this boundary — bare `UInt64`s do not flow past
    `ofTable`. -/
def ofTable (tab : RawDyntab) : Except String DynInfo := do
  let needed := (RawDyntab.findAll tab .needed).map (⟨·.d_un⟩)
  let sonameRaw ← single? tab "DT_SONAME" .soname
  let runpathRaw ← single? tab "DT_RUNPATH" .runpath
  let strtab ← pair? tab "DT_STRTAB/DT_STRSZ" "DT_STRTAB" "DT_STRSZ" .strtab .strsz
  let symtabRaw ← single? tab "DT_SYMTAB" .symtab
  let hashRaw ← single? tab "DT_HASH" .hash
  let rela ← pair? tab "DT_RELA/DT_RELASZ" "DT_RELA" "DT_RELASZ" .rela .relasz
  let jmprel ← pair? tab "DT_JMPREL/DT_PLTRELSZ" "DT_JMPREL" "DT_PLTRELSZ" .jmprel .pltrelsz
  let initArr ← pair? tab "DT_INIT_ARRAY/DT_INIT_ARRAYSZ" "DT_INIT_ARRAY"
    "DT_INIT_ARRAYSZ" .initArray .initArraySz
  let finiArr ← pair? tab "DT_FINI_ARRAY/DT_FINI_ARRAYSZ" "DT_FINI_ARRAY"
    "DT_FINI_ARRAYSZ" .finiArray .finiArraySz
  if strtab.isNone && (needed.size != 0 || sonameRaw.isSome || runpathRaw.isSome) then
    .error "parse: dynamic string references present without DT_STRTAB/DT_STRSZ"
  else
    let symtab : Option Vaddr ←
      match symtabRaw, hashRaw with
      | none, none       => .ok none
      | some sym, some _ => .ok (some ⟨sym⟩)
      | some _, none     => .error "parse: DT_SYMTAB present without DT_HASH"
      | none, some _     => .error "parse: DT_HASH present without DT_SYMTAB"
    let hash := hashRaw.map Vaddr.mk
    return {
      needed
      soname  := sonameRaw.map StrtabOff.mk
      runpath := runpathRaw.map StrtabOff.mk
      strtab, symtab, hash, rela, jmprel, initArr, finiArr
    }

end DynInfo

end LeanLoad.Parse

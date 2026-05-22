/-
One-shot projection of `RawDyntab` — `Parse.RawElf.parse`'s layer 2.

Every section-locating tag this loader consults is resolved here,
into a single record of `(vaddr [× size])` pointers. After
`DynInfo.ofTable`, layer 3 reads `DynInfo` fields directly and the
raw `.dynamic` array is no longer referenced.

The `(DT_X, DT_XSZ)` pairing lives here, not in `parse`. That
isolates "which tag means what" from "where in the file is that
bytes" — `parse` becomes a straight `RawEhdr → Array RawPhdr →
RawDyntab → DynInfo → layer-3 reads` pipeline.

DynInfo is parse-internal: it's not exposed on `RawElf` (the raw
`.dynamic` array isn't carried past `parse`). Each field's
resolved value either flows directly into a `RawElf` field or
drives a layer-3 read.

Three kinds of `UInt64` are present and intentionally distinguished
in the per-field docstrings:

  • **strtab byte-offset** (`needed`, `soname`, `runpath`) — index
    into the parsed `.dynstr` buffer; `RawStrtab.lookup` consumes
    these directly. *Not* a file offset, *not* a vaddr.

  • **vaddr** (`strtab.1`, `symtab`, `hash`, `rela.1`, `jmprel.1`,
    `initArr.1`, `finiArr.1`) — virtual address as recorded in
    `.dynamic`; `vaToOffset` translates it to a file offset at
    layer-3 read time.

  • **byte size** (`strtab.2`, `rela.2`, `jmprel.2`, `initArr.2`,
    `finiArr.2`) — section length in bytes; entry count derives
    from `size / entrySize`.

`DT_RPATH` is **intentionally not honoured** (gabi 08 deprecates
it; `Discover/IO.lean` and `Runtime.c` refuse to honour it too).
`runpath` is set from `DT_RUNPATH` alone — a DT_RPATH-only object
yields `runpath = none`.
-/

import LeanLoad.Parse.Dynamic.RawDyn
import LeanLoad.Parse.Offsets

namespace LeanLoad.Parse

/-- Projection of a parsed `.dynamic` array. Each field holds the
    resolved value (or pair) for one section-locating tag.

    Three semantic kinds of `UInt64` are present (see file header):
    strtab byte-offset, vaddr, byte size. Per-field docstrings
    name the kind explicitly. -/
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
  strtab  : Option (Vaddr × UInt64)
  /-- `DT_SYMTAB` vaddr. Entry count comes from `DT_HASH.nchain`,
      not from any `DT_*SZ` tag. -/
  symtab  : Option Vaddr
  /-- `DT_HASH` vaddr. First 8 bytes are a `RawHash` header; only
      `nchain` is read (sizes the symtab). -/
  hash    : Option Vaddr
  /-- `(DT_RELA vaddr, DT_RELASZ byte-size)`. -/
  rela    : Option (Vaddr × UInt64)
  /-- `(DT_JMPREL vaddr, DT_PLTRELSZ byte-size)`. -/
  jmprel  : Option (Vaddr × UInt64)
  /-- `(DT_INIT_ARRAY vaddr, DT_INIT_ARRAYSZ byte-size)`. -/
  initArr : Option (Vaddr × UInt64)
  /-- `(DT_FINI_ARRAY vaddr, DT_FINI_ARRAYSZ byte-size)`. -/
  finiArr : Option (Vaddr × UInt64)
  deriving Inhabited

/-- Resolve every section-locating tag in one pass. Absent tags
    become `none`. `DT_RPATH` is **not** consulted — see `runpath`'s
    docstring. After this, `parse` no longer touches the raw array.

    Each `d_un` value is wrapped into its semantic type (`StrtabOff`
    or `Vaddr`) at this boundary — bare `UInt64`s do not flow past
    `ofTable`. -/
def DynInfo.ofTable (tab : RawDyntab) : DynInfo :=
  open RawDyntab in
  let asVS : Option (UInt64 × UInt64) → Option (Vaddr × UInt64) :=
    (·.map fun (v, s) => (⟨v⟩, s))
  { needed  := (findAll tab DT_NEEDED).map (⟨·.d_un⟩)
    soname  := (val? tab DT_SONAME).map StrtabOff.mk
    runpath := (val? tab DT_RUNPATH).map StrtabOff.mk
    strtab  := asVS (pair? tab DT_STRTAB DT_STRSZ)
    symtab  := (val? tab DT_SYMTAB).map Vaddr.mk
    hash    := (val? tab DT_HASH).map Vaddr.mk
    rela    := asVS (pair? tab DT_RELA DT_RELASZ)
    jmprel  := asVS (pair? tab DT_JMPREL DT_PLTRELSZ)
    initArr := asVS (pair? tab DT_INIT_ARRAY DT_INIT_ARRAYSZ)
    finiArr := asVS (pair? tab DT_FINI_ARRAY DT_FINI_ARRAYSZ) }

namespace DynInfo

section Example

private def parsedInfo : Option DynInfo :=
  (Parser.run RawDyntab.fixtureBytes
    (RawDyntab.parseTable 0 RawDyntab.fixtureBytes.size)).toOption.map ofTable

#guard parsedInfo.map (·.needed)  = some #[(0x01 : StrtabOff)]
#guard parsedInfo.map (·.soname)  = some (some (0x12 : StrtabOff))
#guard parsedInfo.map (·.runpath) = some (some (0x1b : StrtabOff))  -- DT_RUNPATH present
#guard parsedInfo.map (·.strtab)  = some (some ((0xb0 : Vaddr), 31))
#guard parsedInfo.map (·.symtab)  = some (some (0xd0 : Vaddr))
#guard parsedInfo.map (·.hash)    = some (some (0x100 : Vaddr))
#guard parsedInfo.map (·.rela)    = some (some ((0x108 : Vaddr), 24))
#guard parsedInfo.map (·.jmprel)  = some none                       -- absent
#guard parsedInfo.map (·.initArr) = some (some ((0x120 : Vaddr), 8))
#guard parsedInfo.map (·.finiArr) = some none                       -- absent

-- `DT_RPATH` is intentionally not consulted: a table with only
-- `DT_RPATH` (no `DT_RUNPATH`) yields `runpath = none`. README
-- + `Discover/IO.lean` + `Runtime.c` all agree on this policy;
-- the Parse layer enforces it by simply not reading `DT_RPATH`.
private def rpathOnlyTab : RawDyntab := #[
  { d_tag := DT_RPATH, d_un := 0x42 },
  { d_tag := DT_NULL,  d_un := 0 } ]

#guard (DynInfo.ofTable rpathOnlyTab).runpath = none

end Example

end DynInfo

end LeanLoad.Parse

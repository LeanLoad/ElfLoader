/-
Examples and fixture bytes for `.dynamic` parsing and projection.
-/

import LeanLoad.Parse.DynMap.Basic
import LeanLoad.Parse.LoadMap.ElfHeader.Examples
import LeanLoad.Parse.LoadMap.ProgramHeader.Examples

namespace LeanLoad.Parse.Examples

/-- 224-byte `.dynamic` fixture: 14 entries (13 real + DT_NULL
    terminator) describing the consolidated `Parse.Examples.fixtureBytes`
    layout. Dynamic-content locating tags (`DT_STRTAB` / `DT_SYMTAB` /
    ...) carry vaddrs that match the corresponding content's position in
    the consolidated fixture; strtab references (`DT_NEEDED` /
    `DT_SONAME` / `DT_RUNPATH`) carry byte offsets into
    `Strtab.fixtureBytes`. -/
def dynBytes : ByteArray := ⟨#[
  -- DT_NEEDED -> strtab[0x01] ("libc.so.6")
  0x01, 0, 0, 0, 0, 0, 0, 0,    0x01, 0, 0, 0, 0, 0, 0, 0,
  -- DT_SONAME -> strtab[0x12] ("mylib.so")
  0x0e, 0, 0, 0, 0, 0, 0, 0,    0x12, 0, 0, 0, 0, 0, 0, 0,
  -- DT_RUNPATH -> strtab[0x1b] ("lib")
  0x1d, 0, 0, 0, 0, 0, 0, 0,    0x1b, 0, 0, 0, 0, 0, 0, 0,
  -- DT_STRTAB -> 0xb0 / DT_STRSZ -> 31
  0x05, 0, 0, 0, 0, 0, 0, 0,    0xb0, 0, 0, 0, 0, 0, 0, 0,
  0x0a, 0, 0, 0, 0, 0, 0, 0,    0x1f, 0, 0, 0, 0, 0, 0, 0,
  -- DT_SYMTAB -> 0xd0
  0x06, 0, 0, 0, 0, 0, 0, 0,    0xd0, 0, 0, 0, 0, 0, 0, 0,
  -- DT_SYMENT -> 24 (Elf64_Sym)
  0x0b, 0, 0, 0, 0, 0, 0, 0,    0x18, 0, 0, 0, 0, 0, 0, 0,
  -- DT_HASH -> 0x100 (nchain there says symtab has 2 entries)
  0x04, 0, 0, 0, 0, 0, 0, 0,    0x00, 0x01, 0, 0, 0, 0, 0, 0,
  -- DT_RELA -> 0x108 / DT_RELASZ -> 24
  0x07, 0, 0, 0, 0, 0, 0, 0,    0x08, 0x01, 0, 0, 0, 0, 0, 0,
  0x08, 0, 0, 0, 0, 0, 0, 0,    0x18, 0, 0, 0, 0, 0, 0, 0,
  -- DT_RELAENT -> 24 (Elf64_Rela)
  0x09, 0, 0, 0, 0, 0, 0, 0,    0x18, 0, 0, 0, 0, 0, 0, 0,
  -- DT_INIT_ARRAY -> 0x120 / DT_INIT_ARRAYSZ -> 8
  0x19, 0, 0, 0, 0, 0, 0, 0,    0x20, 0x01, 0, 0, 0, 0, 0, 0,
  0x1b, 0, 0, 0, 0, 0, 0, 0,    0x08, 0, 0, 0, 0, 0, 0, 0,
  -- DT_NULL terminator
  0x00, 0, 0, 0, 0, 0, 0, 0,    0x00, 0, 0, 0, 0, 0, 0, 0
]⟩

#guard dynBytes.size == 14 * (Decodable.byteSize (α := RawEntry)).toNat  -- = 224

-- DT_NEEDED appears three times: gabi 08 allows repetition (one entry per
-- NEEDED library). The integration `dynBytes` below has only one DT_NEEDED,
-- so this unit-level fixture exercises `findAll`'s multi-match path.
private def rawLookupTab : RawDyntab := #[
  { d_tag := .needed, d_un := 0x10 },
  { d_tag := .runpath, d_un := 0x20 },
  { d_tag := .needed, d_un := 0x30 },
  { d_tag := .needed, d_un := 0x40 },
  { d_tag := .null,   d_un := 0 } ]

#guard RawDyntab.val? rawLookupTab .needed  = some 0x10
#guard RawDyntab.val? rawLookupTab .runpath = some 0x20
#guard RawDyntab.val? rawLookupTab .hash    = none

#guard (RawDyntab.findAll rawLookupTab .needed).map (·.d_un) = #[0x10, 0x30, 0x40]
#guard (RawDyntab.findAll rawLookupTab .hash).size           = 0

def rawDyntab? : Option RawDyntab :=
  (RawDyntab.decoder (ByteSize.ofNat dynBytes.size)).decode? dynBytes

#guard rawDyntab?.isSome

def rawDyntab : RawDyntab :=
  rawDyntab?.get (by native_decide)

-- 14 entries total, including the DT_NULL terminator.
#guard rawDyntab.size = 14

-- Strtab references resolve to the documented offsets.
#guard RawDyntab.val? rawDyntab .needed  = some 0x01  -- "libc.so.6"
#guard RawDyntab.val? rawDyntab .soname  = some 0x12  -- "mylib.so"
#guard RawDyntab.val? rawDyntab .runpath = some 0x1b  -- "lib"

-- Dynamic-content locating tags carry the right vaddrs / sizes.
#guard RawDyntab.val? rawDyntab .strtab  = some 0xb0
#guard RawDyntab.val? rawDyntab .strsz   = some 31
#guard RawDyntab.val? rawDyntab .symtab  = some 0xd0
#guard RawDyntab.val? rawDyntab .hash    = some 0x100

-- Tags absent from this fixture return `none`.
#guard RawDyntab.val? rawDyntab .rpath     = none
#guard RawDyntab.val? rawDyntab .jmprel    = none
#guard RawDyntab.val? rawDyntab .finiArray = none

private def loadMap? : Option (LoadMap 0x208) :=
  (LoadMap.ofHeaders 0x208 ehdr programHeaders).toOption

#guard loadMap?.isSome

private def loadMap : LoadMap 0x208 :=
  loadMap?.get (by native_decide)

#guard
  match DynMap.ofRawDyntab #[] loadMap with
  | .ok map => map.needed.isEmpty && map.strtab.isNone && map.symtab.isNone
  | .error _ => false

def dynMap? : Option (DynMap 0x208) :=
  (DynMap.decoder loadMap (ByteSize.ofNat dynBytes.size)).decode? dynBytes

#guard dynMap?.isSome

def dynMap : DynMap 0x208 :=
  dynMap?.get (by native_decide)

#guard dynMap.needed = #[(0x01 : StrtabOff)]
#guard dynMap.soname = some (0x12 : StrtabOff)
#guard dynMap.rpath = none
#guard dynMap.runpath = some (0x1b : StrtabOff)  -- DT_RUNPATH present
#guard dynMap.strtab.map (fun r => (r.off, r.size)) = some ((0xb0 : FileOff), (31 : ByteSize))
#guard dynMap.symtab = some (0xd0 : Eaddr)
#guard dynMap.hash.map (fun r => (r.off, r.size)) =
  some ((0x100 : FileOff), RawSysVHash.byteSize)
#guard dynMap.rela.map (fun r => (r.off, r.size)) =
  some ((0x108 : FileOff), (24 : ByteSize))
#guard dynMap.jmprel = none
#guard dynMap.initArr.map (fun r => (r.off, r.size)) =
  some ((0x120 : FileOff), (8 : ByteSize))
#guard dynMap.finiArr = none

-- `DT_RPATH` is recorded separately from `DT_RUNPATH`; Discover.Search decides
-- whether it participates in the gABI search order.
private def rpathOnlyTab : RawDyntab := #[
  { d_tag := .rpath, d_un := 0x42 },
  { d_tag := .null,  d_un := 0 } ]

#guard
  match DynMap.ofRawDyntab rpathOnlyTab loadMap with
  | .ok map => map.rpath = some (0x42 : StrtabOff) && map.runpath = none
  | .error _ => false

private def duplicateRunpathTab : RawDyntab := #[
  { d_tag := .runpath, d_un := 0x01 },
  { d_tag := .runpath, d_un := 0x02 },
  { d_tag := .null,    d_un := 0 } ]

#guard
  match DynMap.ofRawDyntab duplicateRunpathTab loadMap with
  | .ok _    => false
  | .error _ => true

private def partialRelaTab : RawDyntab := #[
  { d_tag := .rela, d_un := 0x1000 },
  { d_tag := .null, d_un := 0 } ]

#guard
  match DynMap.ofRawDyntab partialRelaTab loadMap with
  | .ok _    => false
  | .error _ => true

private def symtabWithoutSymentTab : RawDyntab := #[
  { d_tag := .strtab, d_un := 0x1000 },
  { d_tag := .strsz,  d_un := 0x20 },
  { d_tag := .symtab, d_un := 0x2000 },
  { d_tag := .null,   d_un := 0 } ]

#guard
  match DynMap.ofRawDyntab symtabWithoutSymentTab loadMap with
  | .ok _    => false
  | .error _ => true

-- Truncated entry: 10 bytes when 16 expected; EOF inside the `d_un` u64 read.
#guard
  (Decodable.decode (α := RawEntry) (dynBytes.extract 0 10)).toOption.isNone

-- Zero-byte `.dynamic` has no mandatory DT_NULL terminator, so parsing fails.
#guard
  (RawDyntab.decoder 0).decode? dynBytes |>.isNone

-- `RawDyntab.decoder` short-circuits at DT_NULL even if more bytes follow:
-- here we point it at 224 bytes; DT_NULL sits at offset 208 (entry 13).
-- The returned array has 14 entries (13 real + the terminator).
#guard
  ((RawDyntab.decoder 224).decode? dynBytes).map (·.size) = some 14

end LeanLoad.Parse.Examples

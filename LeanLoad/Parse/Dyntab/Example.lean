/-
Examples and fixture bytes for `.dynamic` parsing and projection.
-/

import LeanLoad.Parse.Dyntab.Info

namespace LeanLoad.Parse.Example

/-- 192-byte `.dynamic` fixture: 12 entries (11 real + DT_NULL
    terminator) describing the consolidated `Parse.Elf.Example.fixtureBytes`
    layout. Dynamic-content locating tags (`DT_STRTAB` / `DT_SYMTAB` /
    …) carry vaddrs that match the corresponding content's position in
    the consolidated fixture; strtab references (`DT_NEEDED` /
    `DT_SONAME` / `DT_RUNPATH`) carry byte offsets into
    `RawStrtab.fixtureBytes`. -/
def dynBytes : ByteArray := ⟨#[
  -- DT_NEEDED → strtab[0x01] ("libc.so.6")
  0x01, 0, 0, 0, 0, 0, 0, 0,    0x01, 0, 0, 0, 0, 0, 0, 0,
  -- DT_SONAME → strtab[0x12] ("mylib.so")
  0x0e, 0, 0, 0, 0, 0, 0, 0,    0x12, 0, 0, 0, 0, 0, 0, 0,
  -- DT_RUNPATH → strtab[0x1b] ("lib")
  0x1d, 0, 0, 0, 0, 0, 0, 0,    0x1b, 0, 0, 0, 0, 0, 0, 0,
  -- DT_STRTAB → 0xb0 / DT_STRSZ → 31
  0x05, 0, 0, 0, 0, 0, 0, 0,    0xb0, 0, 0, 0, 0, 0, 0, 0,
  0x0a, 0, 0, 0, 0, 0, 0, 0,    0x1f, 0, 0, 0, 0, 0, 0, 0,
  -- DT_SYMTAB → 0xd0
  0x06, 0, 0, 0, 0, 0, 0, 0,    0xd0, 0, 0, 0, 0, 0, 0, 0,
  -- DT_HASH → 0x100 (nchain there says symtab has 2 entries)
  0x04, 0, 0, 0, 0, 0, 0, 0,    0x00, 0x01, 0, 0, 0, 0, 0, 0,
  -- DT_RELA → 0x108 / DT_RELASZ → 24
  0x07, 0, 0, 0, 0, 0, 0, 0,    0x08, 0x01, 0, 0, 0, 0, 0, 0,
  0x08, 0, 0, 0, 0, 0, 0, 0,    0x18, 0, 0, 0, 0, 0, 0, 0,
  -- DT_INIT_ARRAY → 0x120 / DT_INIT_ARRAYSZ → 8
  0x19, 0, 0, 0, 0, 0, 0, 0,    0x20, 0x01, 0, 0, 0, 0, 0, 0,
  0x1b, 0, 0, 0, 0, 0, 0, 0,    0x08, 0, 0, 0, 0, 0, 0, 0,
  -- DT_NULL — terminator
  0x00, 0, 0, 0, 0, 0, 0, 0,    0x00, 0, 0, 0, 0, 0, 0, 0
]⟩

#guard dynBytes.size == 12 * RawDynSize  -- = 192

-- ── Lookup helpers over a manually-built `Array RawDyn` ────────────────
-- DT_NEEDED appears three times: gabi 08 allows repetition (one entry
-- per NEEDED library). The integration `dynBytes` below has only one
-- DT_NEEDED, so this unit-level fixture is what exercises `findAll`'s
-- multi-match path.
private def dynLookupTab : RawDyntab := #[
  { d_tag := .needed, d_un := 0x10 },
  { d_tag := .runpath, d_un := 0x20 },
  { d_tag := .needed, d_un := 0x30 },
  { d_tag := .needed, d_un := 0x40 },
  { d_tag := .null,   d_un := 0 } ]

#guard RawDyntab.val? dynLookupTab .needed  = some 0x10
#guard RawDyntab.val? dynLookupTab .runpath = some 0x20
#guard RawDyntab.val? dynLookupTab .hash    = none

#guard (RawDyntab.findAll dynLookupTab .needed).map (·.d_un) = #[0x10, 0x30, 0x40]
#guard (RawDyntab.findAll dynLookupTab .hash).size           = 0

-- ── `RawDyntab.parse` over `dynBytes` + post-parse lookups ────────────

def dyntab? : Option RawDyntab :=
  parseBytes? dynBytes (RawDyntab.parse (ByteSize.ofNat dynBytes.size))

#guard dyntab?.isSome

def dyntab : RawDyntab :=
  dyntab?.get (by native_decide)

-- 12 entries total, including the DT_NULL terminator.
#guard dyntab.size = 12

-- Strtab references resolve to the documented offsets.
#guard RawDyntab.val? dyntab .needed  = some 0x01  -- "libc.so.6"
#guard RawDyntab.val? dyntab .soname  = some 0x12  -- "mylib.so"
#guard RawDyntab.val? dyntab .runpath = some 0x1b  -- "lib"

-- Dynamic-content locating tags carry the right vaddrs / sizes.
#guard RawDyntab.val? dyntab .strtab  = some 0xb0
#guard RawDyntab.val? dyntab .strsz   = some 31
#guard RawDyntab.val? dyntab .symtab  = some 0xd0
#guard RawDyntab.val? dyntab .hash    = some 0x100

-- Tags absent from this fixture return `none`.
#guard RawDyntab.val? dyntab .rpath     = none
#guard RawDyntab.val? dyntab .jmprel    = none
#guard RawDyntab.val? dyntab .finiArray = none

-- ── DynInfo projection ────────────────────────────────────────────────

def dynInfo? : Option DynInfo :=
  (DynInfo.ofTable dyntab).toOption

#guard dynInfo?.isSome

def dynInfo : DynInfo :=
  dynInfo?.get (by native_decide)

#guard dynInfo.needed  = #[(0x01 : StrtabOff)]
#guard dynInfo.soname  = some (0x12 : StrtabOff)
#guard dynInfo.runpath = some (0x1b : StrtabOff)  -- DT_RUNPATH present
#guard dynInfo.strtab  = some ((0xb0 : Vaddr), 31)
#guard dynInfo.symtab  = some (0xd0 : Vaddr)
#guard dynInfo.hash    = some (0x100 : Vaddr)
#guard dynInfo.rela    = some ((0x108 : Vaddr), 24)
#guard dynInfo.jmprel  = none
#guard dynInfo.initArr = some ((0x120 : Vaddr), 8)
#guard dynInfo.finiArr = none

-- `DT_RPATH` is intentionally not consulted: a table with only
-- `DT_RPATH` (no `DT_RUNPATH`) yields `runpath = none`. README
-- + `Discover/IO.lean` + `Runtime.c` all agree on this policy;
-- the Parse layer enforces it by simply not reading `DT_RPATH`.
private def rpathOnlyTab : RawDyntab := #[
  { d_tag := .rpath, d_un := 0x42 },
  { d_tag := .null,  d_un := 0 } ]

#guard
  match DynInfo.ofTable rpathOnlyTab with
  | .ok info => info.runpath = none
  | .error _ => false

private def duplicateRunpathTab : RawDyntab := #[
  { d_tag := .runpath, d_un := 0x01 },
  { d_tag := .runpath, d_un := 0x02 },
  { d_tag := .null,    d_un := 0 } ]

#guard
  match DynInfo.ofTable duplicateRunpathTab with
  | .ok _    => false
  | .error _ => true

private def partialRelaTab : RawDyntab := #[
  { d_tag := .rela, d_un := 0x1000 },
  { d_tag := .null, d_un := 0 } ]

#guard
  match DynInfo.ofTable partialRelaTab with
  | .ok _    => false
  | .error _ => true

private def symtabWithoutHashTab : RawDyntab := #[
  { d_tag := .strtab, d_un := 0x1000 },
  { d_tag := .strsz,  d_un := 0x20 },
  { d_tag := .symtab, d_un := 0x2000 },
  { d_tag := .null,   d_un := 0 } ]

#guard
  match DynInfo.ofTable symtabWithoutHashTab with
  | .ok _    => false
  | .error _ => true

-- ── Error cases ──────────────────────────────────────────────────────
-- Truncated entry: 10 bytes when 16 (RawDynSize) expected — EOF inside
-- the `d_un` u64 read.
#guard
  (decodeBytes? (α := RawDyn) (dynBytes.extract 0 10)).isNone

-- Zero-byte `.dynamic` has no mandatory DT_NULL terminator, so parsing fails.
#guard
  (parseBytes? dynBytes (RawDyntab.parse 0)).isNone

-- `RawDyntab.parse` short-circuits at DT_NULL even if more bytes follow:
-- here we point it at 192 bytes; DT_NULL sits at offset 176 (entry 11).
-- The returned array has 12 entries (11 real + the terminator).
#guard
  (parseBytes? dynBytes (RawDyntab.parse 192)).map (·.size) = some 12

end LeanLoad.Parse.Example

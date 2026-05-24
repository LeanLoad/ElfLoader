/-
Examples and fixture bytes for `.dynamic` parsing and projection.
-/

import LeanLoad.Parse.Dynamic.Dyntab.Basic

namespace LeanLoad.Parse.Examples

/-- 224-byte `.dynamic` fixture: 14 entries (13 real + DT_NULL
    terminator) describing the consolidated `Parse.Examples.fixtureBytes`
    layout. Dynamic-content locating tags (`DT_STRTAB` / `DT_SYMTAB` /
    …) carry vaddrs that match the corresponding content's position in
    the consolidated fixture; strtab references (`DT_NEEDED` /
    `DT_SONAME` / `DT_RUNPATH`) carry byte offsets into
    `Strtab.fixtureBytes`. -/
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
  -- DT_SYMENT → 24 (Elf64_Sym)
  0x0b, 0, 0, 0, 0, 0, 0, 0,    0x18, 0, 0, 0, 0, 0, 0, 0,
  -- DT_HASH → 0x100 (nchain there says symtab has 2 entries)
  0x04, 0, 0, 0, 0, 0, 0, 0,    0x00, 0x01, 0, 0, 0, 0, 0, 0,
  -- DT_RELA → 0x108 / DT_RELASZ → 24
  0x07, 0, 0, 0, 0, 0, 0, 0,    0x08, 0x01, 0, 0, 0, 0, 0, 0,
  0x08, 0, 0, 0, 0, 0, 0, 0,    0x18, 0, 0, 0, 0, 0, 0, 0,
  -- DT_RELAENT → 24 (Elf64_Rela)
  0x09, 0, 0, 0, 0, 0, 0, 0,    0x18, 0, 0, 0, 0, 0, 0, 0,
  -- DT_INIT_ARRAY → 0x120 / DT_INIT_ARRAYSZ → 8
  0x19, 0, 0, 0, 0, 0, 0, 0,    0x20, 0x01, 0, 0, 0, 0, 0, 0,
  0x1b, 0, 0, 0, 0, 0, 0, 0,    0x08, 0, 0, 0, 0, 0, 0, 0,
  -- DT_NULL — terminator
  0x00, 0, 0, 0, 0, 0, 0, 0,    0x00, 0, 0, 0, 0, 0, 0, 0
]⟩

#guard dynBytes.size == 14 * Decodable.byteSize (α := Dyntab.Entry)  -- = 224

-- ── Lookup helpers over a manually-built `Dyntab` ─────────────────────
-- DT_NEEDED appears three times: gabi 08 allows repetition (one entry
-- per NEEDED library). The integration `dynBytes` below has only one
-- DT_NEEDED, so this unit-level fixture is what exercises `findAll`'s
-- multi-match path.
private def dynLookupTab : Dyntab := #[
  { d_tag := .needed, d_un := 0x10 },
  { d_tag := .runpath, d_un := 0x20 },
  { d_tag := .needed, d_un := 0x30 },
  { d_tag := .needed, d_un := 0x40 },
  { d_tag := .null,   d_un := 0 } ]

#guard Dyntab.val? dynLookupTab .needed  = some 0x10
#guard Dyntab.val? dynLookupTab .runpath = some 0x20
#guard Dyntab.val? dynLookupTab .hash    = none

#guard (Dyntab.findAll dynLookupTab .needed).map (·.d_un) = #[0x10, 0x30, 0x40]
#guard (Dyntab.findAll dynLookupTab .hash).size           = 0

-- ── `Dyntab.decode` over `dynBytes` + post-decode lookups ───────────────

def dyntab? : Option Dyntab :=
  Decoder.run? dynBytes (Dyntab.decode (ByteSize.ofNat dynBytes.size))

#guard dyntab?.isSome

def dyntab : Dyntab :=
  dyntab?.get (by native_decide)

-- 14 entries total, including the DT_NULL terminator.
#guard dyntab.size = 14

-- Strtab references resolve to the documented offsets.
#guard Dyntab.val? dyntab .needed  = some 0x01  -- "libc.so.6"
#guard Dyntab.val? dyntab .soname  = some 0x12  -- "mylib.so"
#guard Dyntab.val? dyntab .runpath = some 0x1b  -- "lib"

-- Dynamic-content locating tags carry the right vaddrs / sizes.
#guard Dyntab.val? dyntab .strtab  = some 0xb0
#guard Dyntab.val? dyntab .strsz   = some 31
#guard Dyntab.val? dyntab .symtab  = some 0xd0
#guard Dyntab.val? dyntab .hash    = some 0x100

-- Tags absent from this fixture return `none`.
#guard Dyntab.val? dyntab .rpath     = none
#guard Dyntab.val? dyntab .jmprel    = none
#guard Dyntab.val? dyntab .finiArray = none

-- ── Typed dynamic-table accessors ─────────────────────────────────────

private def okEq [BEq α] (actual : Except String α) (expected : α) : Bool :=
  match actual with
  | .ok got   => got == expected
  | .error _  => false

#guard dyntab.needed = #[(0x01 : StrtabOff)]
#guard okEq dyntab.soname? (some (0x12 : StrtabOff))
#guard okEq dyntab.runpath? (some (0x1b : StrtabOff))  -- DT_RUNPATH present
#guard okEq dyntab.strtab? (some ({ start := (0xb0 : Eaddr), size := 31 } : EaddrRange))
#guard okEq dyntab.symtab? (some (0xd0 : Eaddr))
#guard okEq dyntab.hash? (some (0x100 : Eaddr))
#guard okEq dyntab.rela? (some ({ start := (0x108 : Eaddr), size := 24 } : EaddrRange))
#guard okEq dyntab.jmprel? none
#guard okEq dyntab.pltrel? none
#guard okEq dyntab.initArr? (some ({ start := (0x120 : Eaddr), size := 8 } : EaddrRange))
#guard okEq dyntab.finiArr? none

-- `DT_RPATH` is intentionally not consulted: a table with only
-- `DT_RPATH` (no `DT_RUNPATH`) yields `runpath = none`. README
-- + the production object finder + `Runtime.c` all agree on this policy;
-- the Parse layer enforces it by simply not reading `DT_RPATH`.
private def rpathOnlyTab : Dyntab := #[
  { d_tag := .rpath, d_un := 0x42 },
  { d_tag := .null,  d_un := 0 } ]

#guard
  match rpathOnlyTab.runpath? with
  | .ok runpath => runpath = none
  | .error _ => false

private def duplicateRunpathTab : Dyntab := #[
  { d_tag := .runpath, d_un := 0x01 },
  { d_tag := .runpath, d_un := 0x02 },
  { d_tag := .null,    d_un := 0 } ]

#guard
  match duplicateRunpathTab.runpath? with
  | .ok _    => false
  | .error _ => true

private def partialRelaTab : Dyntab := #[
  { d_tag := .rela, d_un := 0x1000 },
  { d_tag := .null, d_un := 0 } ]

#guard
  match partialRelaTab.rela? with
  | .ok _    => false
  | .error _ => true

private def symtabWithoutSymentTab : Dyntab := #[
  { d_tag := .strtab, d_un := 0x1000 },
  { d_tag := .strsz,  d_un := 0x20 },
  { d_tag := .symtab, d_un := 0x2000 },
  { d_tag := .null,   d_un := 0 } ]

#guard
  match symtabWithoutSymentTab.symtab? with
  | .ok _    => false
  | .error _ => true

-- ── Error cases ──────────────────────────────────────────────────────
-- Truncated entry: 10 bytes when 16 expected — EOF inside the `d_un` u64 read.
#guard
  (Decoder.run? (dynBytes.extract 0 10) (Decodable.decode (α := Dyntab.Entry))).isNone

-- Zero-byte `.dynamic` has no mandatory DT_NULL terminator, so parsing fails.
#guard
  (Decoder.run? dynBytes (Dyntab.decode 0)).isNone

-- `Dyntab.decode` short-circuits at DT_NULL even if more bytes follow:
-- here we point it at 224 bytes; DT_NULL sits at offset 208 (entry 13).
-- The returned array has 14 entries (13 real + the terminator).
#guard
  (Decoder.run? dynBytes (Dyntab.decode 224)).map (·.size) = some 14

end LeanLoad.Parse.Examples

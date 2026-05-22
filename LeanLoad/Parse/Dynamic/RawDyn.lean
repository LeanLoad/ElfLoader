/-
gabi 08 § Dynamic Section — `Elf64_Dyn` entry, plus the `.dynamic`
array parser and by-tag lookups.

Spec: gabi 08 (`third_party/gabi/docsrc/elf/08-dynamic.rst`).

`d_tag` constants kept here are only those `Parse.RawElf.parse` uses
navigationally (find each section in the `.dynamic` array).
Interpretive constants (`DT_FLAGS`, `DF_*`, etc.) live in `Elaborate`.

The `.dynamic` array is `DT_NULL`-terminated, so it can't use the
generic `decodeArray` (fixed-count) — `RawDyntab.parseTable` below
is the dedicated parser. `RawDyntab.findAll / val? / pair?` are
post-parse lookups over the resulting `RawDyntab`. The one-shot
projection into a record of section pointers lives in
`Parse/DynInfo.lean`.
-/

import LeanLoad.Parse.Decode
import LeanLoad.Parse.Deriving

namespace LeanLoad.Parse

/-- One entry of the `.dynamic` array. `d_un` holds either `d_val`
    (an integer) or `d_ptr` (a virtual address); the interpretation
    is controlled by `d_tag`. -/
structure RawDyn where
  d_tag : UInt64
  d_un  : UInt64
  deriving Repr, Inhabited, BytesDecode

/-- Size of one `Elf64_Dyn` on disk: 8+8 = 16. -/
def RawDynSize : Nat := 16


/-- Parsed `.dynamic` array — `DT_NULL`-terminated sequence of
    `RawDyn` entries. Lookups via `RawDyntab.findAll / val? / pair?`;
    one-shot projection into `DynInfo` via `DynInfo.ofTable`. -/
abbrev RawDyntab := Array RawDyn

-- ============================================================================
-- DT_* tag constants. Only the values `Parse.RawElf.parse` uses to
-- locate sections — full DT vocabulary lives in `Elaborate`.
-- ============================================================================

def DT_NULL          : UInt64 := 0
def DT_NEEDED        : UInt64 := 1
def DT_PLTRELSZ      : UInt64 := 2
def DT_HASH          : UInt64 := 4
def DT_STRTAB        : UInt64 := 5
def DT_SYMTAB        : UInt64 := 6
def DT_RELA          : UInt64 := 7
def DT_RELASZ        : UInt64 := 8
def DT_STRSZ         : UInt64 := 10
def DT_SONAME        : UInt64 := 14
def DT_RPATH         : UInt64 := 15
def DT_JMPREL        : UInt64 := 23
def DT_INIT_ARRAY    : UInt64 := 25
def DT_FINI_ARRAY    : UInt64 := 26
def DT_INIT_ARRAYSZ  : UInt64 := 27
def DT_FINI_ARRAYSZ  : UInt64 := 28
def DT_RUNPATH       : UInt64 := 29

namespace RawDyntab

-- ============================================================================
-- `.dynamic` array parser. `parseTable` chains a fuel-bounded loop
-- (`collect`) that decodes one `RawDyn` at a time until DT_NULL or
-- `limit`, whichever comes first.
-- ============================================================================

/-- Read entries up to and including `DT_NULL`, or until `limit`
    bytes have been consumed. -/
private def collect (fuel : Nat) (limit : Nat) (acc : RawDyntab) :
    Parser RawDyntab := do
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
def parseTable (offset bytes : Nat) : Parser RawDyntab := do
  seek offset
  collect bytes (offset + bytes) (Array.mkEmpty 16)

-- ============================================================================
-- Lookup helpers over a parsed `.dynamic` array.
-- ============================================================================

/-- All entries matching a tag (e.g. all `DT_NEEDED`). -/
def findAll (tab : RawDyntab) (tag : UInt64) : RawDyntab :=
  tab.filter (·.d_tag == tag)

/-- Value of the first entry with `tag`, or `none`. -/
def val? (tab : RawDyntab) (tag : UInt64) : Option UInt64 :=
  (tab.find? (·.d_tag == tag)).map (·.d_un)

/-- Values of two tags as a pair, `none` if either is absent.
    Used to read `(addr, size)`-style sized sections like
    `(DT_RELA, DT_RELASZ)` in one shot. -/
def pair? (tab : RawDyntab) (tagA tagB : UInt64) : Option (UInt64 × UInt64) := do
  let a ← val? tab tagA
  let b ← val? tab tagB
  return (a, b)

/-- 192-byte `.dynamic` fixture: 12 entries (11 real + DT_NULL
    terminator) describing the consolidated `Parse.RawElf.fixtureBytes`
    layout. Section-locating tags (`DT_STRTAB` / `DT_SYMTAB` / …)
    carry vaddrs that match the corresponding section's position in
    the consolidated fixture; strtab references (`DT_NEEDED` /
    `DT_SONAME` / `DT_RUNPATH`) carry byte offsets into
    `Parse.RawStrtab.fixtureBytes`. -/
def fixtureBytes : ByteArray := ⟨#[
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

#guard fixtureBytes.size == 12 * RawDynSize  -- = 192

section Example

-- ── Lookup helpers over a manually-built `Array RawDyn` ────────────────
-- DT_NEEDED appears three times: gabi 08 allows repetition (one entry
-- per NEEDED library). The integration `fixtureBytes` below has only
-- one DT_NEEDED, so this unit-level fixture is what exercises
-- `findAll`'s multi-match path.
private def tab : Array RawDyn := #[
  { d_tag := DT_NEEDED, d_un := 0x10 },
  { d_tag := DT_RUNPATH, d_un := 0x20 },
  { d_tag := DT_NEEDED, d_un := 0x30 },
  { d_tag := DT_NEEDED, d_un := 0x40 },
  { d_tag := DT_NULL,   d_un := 0 } ]

#guard val? tab DT_NEEDED  = some 0x10
#guard val? tab DT_RUNPATH = some 0x20
#guard val? tab DT_HASH    = none

#guard (findAll tab DT_NEEDED).map (·.d_un) = #[0x10, 0x30, 0x40]
#guard (findAll tab DT_HASH).size           = 0

#guard pair? tab DT_NEEDED DT_NULL = some (0x10, 0)
#guard pair? tab DT_NEEDED DT_HASH = none

-- ── `parseTable` over `fixtureBytes` + post-parse lookups ──────────────

private def parsedTable : Option (Array RawDyn) :=
  (Parser.run fixtureBytes (parseTable 0 fixtureBytes.size)).toOption

-- 12 entries total, including the DT_NULL terminator.
#guard parsedTable.map (·.size) = some 12

-- Strtab references resolve to the documented offsets.
#guard parsedTable.bind (val? · DT_NEEDED)  = some 0x01  -- "libc.so.6"
#guard parsedTable.bind (val? · DT_SONAME)  = some 0x12  -- "mylib.so"
#guard parsedTable.bind (val? · DT_RUNPATH) = some 0x1b  -- "lib"

-- Section-locating tags carry the right vaddrs / sizes.
#guard parsedTable.bind (val? · DT_STRTAB)  = some 0xb0
#guard parsedTable.bind (val? · DT_STRSZ)   = some 31
#guard parsedTable.bind (val? · DT_SYMTAB)  = some 0xd0
#guard parsedTable.bind (val? · DT_HASH)    = some 0x100

-- `pair?` reads `(addr, size)` pairs in one shot.
#guard parsedTable.bind (pair? · DT_RELA DT_RELASZ)              = some (0x108, 24)
#guard parsedTable.bind (pair? · DT_INIT_ARRAY DT_INIT_ARRAYSZ)  = some (0x120, 8)

-- Tags absent from this fixture return `none`.
#guard parsedTable.bind (val? · DT_RPATH)      = none
#guard parsedTable.bind (val? · DT_JMPREL)     = none
#guard parsedTable.bind (val? · DT_FINI_ARRAY) = none

-- ── Error cases ──────────────────────────────────────────────────────
-- Truncated entry: 10 bytes when 16 (RawDynSize) expected — EOF inside
-- the `d_un` u64 read.
#guard
  (Parser.run (fixtureBytes.extract 0 10) (BytesDecode.decode : Parser RawDyn)).toOption.isNone

-- `parseTable` with `limit < RawDynSize` returns immediately with an
-- empty array (no entries decoded — the `cur >= limit` check fires
-- before the first decode attempt). Not an error, just early return.
#guard
  (Parser.run fixtureBytes (parseTable 0 0)).toOption.map (·.size) = some 0

-- `parseTable` short-circuits at DT_NULL even if more bytes follow:
-- here we point it at 192 bytes; DT_NULL sits at offset 176 (entry 11).
-- The returned array has 12 entries (11 real + the terminator).
#guard
  (Parser.run fixtureBytes (parseTable 0 192)).toOption.map (·.size) = some 12

end Example

end RawDyntab

end LeanLoad.Parse

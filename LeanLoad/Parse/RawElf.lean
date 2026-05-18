/-
Aggregate ELF byte parser: walks an entire ELF the way a loader needs
to — header → program headers → `.dynamic` → string table → dynamic
symbol table → relocation tables → `DT_NEEDED` strings → init/fini
lists.

This file is *only* the byte-decode stage. It returns a `RawElf`
with no semantic checks: malformed PT_LOAD shape, unhost-able
relocations, and unsupported ELF class/endianness are all caught
later by `Elaborate.elaborate`.

The dynamic symbol-table count comes from `DT_HASH`'s `nchain` field
(gabi 08 § Hash Table). Modern toolchains default to `--hash-style=
gnu`, which would emit only `DT_GNU_HASH` and require chain walking;
the build (`Makefile`) requests `--hash-style=both` so `DT_HASH` is
always available, letting this parser stay simple.

Raw types live in `Parse.Raw{Ehdr,Strtab,Sym,Rela,Phdr,Dyn}`. The
`.dynamic` array's variable-length parser and by-tag lookups share
a file with the `RawDyn` struct (`Parse.RawDyn`).
-/

import LeanLoad.Parse.Decode
import LeanLoad.Parse.RawEhdr
import LeanLoad.Parse.RawStrtab
import LeanLoad.Parse.RawSym
import LeanLoad.Parse.RawRela
import LeanLoad.Parse.RawPhdr
import LeanLoad.Parse.RawDyn
import LeanLoad.Runtime

namespace LeanLoad.Parse

-- ============================================================================
-- RawElf — output of `parse`. Bytes decoded only; no witnesses.
--
-- The phdr-array helper `vaToOffset` (virtual-address ↔ file-offset
-- translation, used below by `parseAtVaddr`) lives with the type it
-- operates on, in `Parse/RawPhdr.lean`.
-- ============================================================================

/-- The raw byte-decode of an ELF file. Output of `parse`, input to
    `Elaborate.elaborate`. The `.dynamic` array is fully consumed
    inside `parse` to derive every other field, so it isn't carried
    forward — `Elaborate` and downstream stages never look at it. -/
structure RawElf where
  header  : RawEhdr
  phdrs   : Array RawPhdr
  /-- The dynamic string table (`DT_STRTAB`), empty if absent. -/
  strtab  : RawStrtab
  /-- Dynamic symbol table (`DT_SYMTAB`). Empty if no hash entry
      tells us the count. -/
  symtab  : Array RawSym
  /-- `DT_NEEDED` offsets into `strtab`, in dynamic-array order. -/
  needed  : Array UInt64
  /-- `DT_SONAME` offset into `strtab`, if present. -/
  soname  : Option UInt64
  /-- `DT_RUNPATH` offset into `strtab`, falling back to `DT_RPATH`. -/
  runpath : Option UInt64
  /-- General `Rela` relocations from `DT_RELA`, ungrouped. -/
  rela    : Array RawRela
  /-- PLT relocations from `DT_JMPREL`, ungrouped. -/
  jmprel  : Array RawRela
  /-- `DT_INIT_ARRAY` entries — already parsed from the file bytes. -/
  initArr : Array UInt64
  /-- `DT_FINI_ARRAY` entries — already parsed from the file bytes.
      For ET_DYN, walked in reverse on process exit (mirrors `initArr`'s
      forward walk on startup). -/
  finiArr : Array UInt64
  deriving Inhabited

end LeanLoad.Parse

-- ============================================================================
-- Helpers and the `parse` entry point.
-- ============================================================================

namespace LeanLoad.Parse.RawElf

open LeanLoad
open LeanLoad.Parse
open LeanLoad.Parse.RawDyn (parseTable findAll val? pair?)

/-- Parse an ELF file via per-section `pread`s on a `FileHandle`.
    Each section's bytes live in their own small `ByteArray` and are
    GC'd after parsing — no whole-file `ByteArray` is constructed.

    Internal helpers live as local `let`-bindings that close over `h`
    (always) and `phdrs` / `dyn` (after they're parsed) — so the
    section-reading calls below don't have to thread those args.

    Three layers; each `--` block names where the section's
    (offset, size) comes from:

      Layer 1: chained off the ELF header — offset is literal or from
               `ehdr`'s fields.
      Layer 2: pure projections out of the parsed `.dynamic` array.
      Layer 3: vaddr-keyed reads via `.dynamic` tags, routed through
               `vaToOffset` over the parsed phdrs. -/
def parse (h : Runtime.FileHandle) : IO RawElf := do
  -- ── Helper for the direct-offset case (only `h` in scope yet). ────
  let parseAt {α} (offset len : UInt64) (parser : Parser α) : IO α := do
    let bytes ← Runtime.pread h offset len
    match Parser.run bytes parser with
    | .ok v    => pure v
    | .error e => throw (IO.userError s!"parse: {e}")

  -- ── Layer 1: header → phdrs → .dynamic ────────────────────────────
  let header ← parseAt 0 RawEhdrSize.toUInt64
                 (BytesDecode.decode : Parser RawEhdr)
  let phdrs ← parseAt header.e_phoff
                (header.e_phnum.toNat * RawPhdrSize).toUInt64
                (decodeArray (α := RawPhdr) 0 header.e_phnum.toNat)
  let dyn ← match phdrs.find? (·.p_type == PT_DYNAMIC) with
    | none    => pure #[]
    | some ph => parseAt ph.p_offset ph.p_filesz
                   (parseTable 0 ph.p_filesz.toNat)

  -- ── Vaddr-aware helpers; close over `phdrs` now that it exists. ───
  -- `parseAtVaddr` resolves a vaddr to a file offset via `vaToOffset`
  -- over PT_LOAD coverage, then defers to `parseAt`.
  let parseAtVaddr {α} (vaddr len : UInt64) (parser : Parser α) : IO α :=
    match vaToOffset phdrs vaddr with
    | some off => parseAt off.toUInt64 len parser
    | none     => throw (IO.userError s!"parse: va 0x{vaddr.toNat} not in any PT_LOAD")

  -- `parseArrayAt`: the workhorse for vaddr-routed fixed-size tables.
  -- Args read as "each entry is `entrySize` bytes, table starts at
  -- `vaddr`, has `count` entries"; result is `Array α` decoded
  -- field-by-field via `BytesDecode`.
  let parseArrayAt {α} [BytesDecode α]
      (entrySize : Nat) (vaddr : UInt64) (count : Nat) : IO (Array α) :=
    parseAtVaddr vaddr (count * entrySize).toUInt64
      (decodeArray (α := α) 0 count)

  -- ── Layer 2: pure .dynamic projections ────────────────────────────
  let needed  := (findAll dyn DT_NEEDED).map (·.d_un)
  let soname  := val? dyn DT_SONAME
  let runpath := val? dyn DT_RUNPATH <|> val? dyn DT_RPATH

  -- ── Layer 3: vaddr-keyed sections via `.dynamic` tags ─────────────
  -- symtab count: `nchain` from DT_HASH (`--hash-style=both` ensures
  -- DT_HASH is present; GNU-only would need chain walking).
  let symCount ← match val? dyn DT_HASH with
    | none    => pure 0
    | some va => parseAtVaddr va 8
                   (do skip 4 /- nbucket -/; let nchain ← u32le; return nchain.toNat)
  -- strtab: raw bytes; UTF-8 lookup lives in `RawStrtab.lookup`.
  let strtab ← match pair? dyn DT_STRTAB DT_STRSZ with
    | none       => pure (ByteArray.mk #[])
    | some (v,s) => parseAtVaddr v s buffer
  -- symtab: vaddr from DT_SYMTAB, count from DT_HASH.nchain (the only
  -- section whose size doesn't pair with a DT_*SZ tag).
  let symtab ← if symCount == 0 then pure #[]
               else match val? dyn DT_SYMTAB with
                 | none    => pure #[]
                 | some va => parseArrayAt RawSymSize va symCount
  -- Sized tables — gabi-08's `(DT_X, DT_XSZ)`-keyed cluster: count
  -- comes from `sizeTag / entrySize`.
  let parseSizedTable {α} [BytesDecode α]
      (entrySize : Nat) (addrTag sizeTag : UInt64) : IO (Array α) :=
    match pair? dyn addrTag sizeTag with
    | none       => pure #[]
    | some (v,s) => parseArrayAt entrySize v (s.toNat / entrySize)
  let rela    ← parseSizedTable RawRelaSize DT_RELA       DT_RELASZ
  let jmprel  ← parseSizedTable RawRelaSize DT_JMPREL     DT_PLTRELSZ
  let initArr ← parseSizedTable 8           DT_INIT_ARRAY DT_INIT_ARRAYSZ
  let finiArr ← parseSizedTable 8           DT_FINI_ARRAY DT_FINI_ARRAYSZ

  return {
    header, phdrs, strtab, symtab, needed, soname, runpath,
    rela, jmprel, initArr, finiArr
  }

-- ============================================================================
-- Integration example — a hand-crafted 488-byte ET_DYN that exercises
-- every parser this file chains together.
--
-- Per-struct decoders (RawEhdr / RawPhdr / RawSym / RawRela
-- / RawStrtab / RawDyn) are exercised standalone in their respective
-- files' `section Example` blocks. The fixture here is different: it
-- demonstrates *cross-section coordination* — PT_DYNAMIC's `p_offset`
-- matches the dynamic table's actual position, DT_STRTAB's `d_un`
-- matches the strtab's vaddr, DT_HASH's `nchain` matches the symtab's
-- entry count, and so on. Manually walking these chains is what
-- `parse` does over a real `FileHandle`; here we do it over the same
-- ByteArray.
--
-- The fixture is also engineered to satisfy `elaborate`'s gabi-07
-- checks downstream: the lone PT_LOAD has `vaddr = offset = 0` and
-- covers the phdr table, every rela offset, and every init_array
-- entry. `LeanLoad/Example.lean` consumes `fixture` for the
-- real-world acceptance check at the elaborate boundary.
-- ============================================================================

section Example

-- ---- Per-section fixture bytes ─────────────────────────────────────────
-- The struct-typed sections come from each Raw*.lean's `fixtureBytes`
-- (so a byte change in any per-struct file ripples here automatically).
-- `hashBytes` and `initArrBytes` aren't `RawX`-typed (just raw u32/u64
-- arrays read by `parseSymCount` / `parseSizedTable` in the production
-- path), so they live inline here.

-- Hash section (8 bytes): `nbucket = 1`, `nchain = 2`. `parseSymCount`
-- only reads `nchain` to size the symtab; the bucket/chain arrays a
-- real ELF appends are unused by LeanLoad and omitted.
private def hashBytes : ByteArray := ⟨#[
  0x01, 0x00, 0x00, 0x00,                                       -- nbucket = 1
  0x02, 0x00, 0x00, 0x00                                        -- nchain  = 2
]⟩

-- Init array (8 bytes): one ctor pointer at 0x100 (inside PT_LOAD's
-- executable memsz, so `initArrInExecSeg` accepts at elaborate time).
private def initArrBytes : ByteArray := ⟨#[
  0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
]⟩

-- ---- File layout — section offsets within `fixtureBytes` ──────────────
-- The lone PT_LOAD has `vaddr = offset`, so `vaToOffset` is the
-- identity on this fixture. Sizes derive from each section's bytes
-- so renaming a section's content elsewhere doesn't desync offsets.
private def ehdrEnd    : Nat := RawEhdr.fixtureBytes.size                       -- 64
private def phdrsEnd   : Nat := ehdrEnd + RawPhdr.fixtureBytes.size             -- 0xb0
private def strtabEnd  : Nat := phdrsEnd + RawStrtab.fixtureBytes.size          -- 0xd0
private def symtabEnd  : Nat := strtabEnd + RawSym.fixtureBytes.size            -- 0x100
private def hashEnd    : Nat := symtabEnd + hashBytes.size                      -- 0x108
private def relaEnd    : Nat := hashEnd + RawRela.fixtureBytes.size             -- 0x120
private def initArrEnd : Nat := relaEnd + initArrBytes.size                     -- 0x128
private def fileEnd    : Nat := initArrEnd + RawDyn.fixtureBytes.size           -- 0x1e8

/-- Hand-crafted 488-byte ET_DYN ELF used as the integration fixture.
    Concatenation of every per-struct `fixtureBytes` in file-order,
    interleaved with the non-struct-typed hash + init-array sections.
    The byte content for each typed section lives in the corresponding
    `Parse/Raw*.lean` so changes propagate from a single source of truth. -/
def fixtureBytes : ByteArray :=
  RawEhdr.fixtureBytes
    ++ RawPhdr.fixtureBytes
    ++ RawStrtab.fixtureBytes
    ++ RawSym.fixtureBytes
    ++ hashBytes
    ++ RawRela.fixtureBytes
    ++ initArrBytes
    ++ RawDyn.fixtureBytes

-- Section size sanity (catches any byte miscount across files).
#guard fixtureBytes.size = fileEnd
#guard fileEnd = 0x1e8                  -- 488 bytes total
#guard ehdrEnd = 0x040                  -- 64
#guard phdrsEnd = 0x0b0                 -- 64 + 2*56
#guard strtabEnd = 0x0d0                -- 0xb0 + 32
#guard symtabEnd = 0x100                -- 0xd0 + 48
#guard hashEnd = 0x108                  -- 0x100 + 8
#guard relaEnd = 0x120                  -- 0x108 + 24
#guard initArrEnd = 0x128               -- 0x120 + 8

-- ---- Walk the fixture in `parse`-order, then reassemble ──────────────

/-- Parse-side counterpart to `Parse.RawElf.parse`, but pure: each
    section's offset is plucked from the fixture instead of issued
    through `Runtime.pread`. Returns `none` if any decode step fails.

    This is what `LeanLoad/Example.lean` runs through `elaborate` for
    the real-world acceptance check at the parse → elaborate boundary. -/
def fixture : Option Parse.RawElf := do
  let header  ← (Parser.run fixtureBytes (BytesDecode.decode : Parser RawEhdr)).toOption
  let phdrs   ← (Parser.run fixtureBytes
                    (decodeArray (α := RawPhdr) ehdrEnd header.e_phnum.toNat)).toOption
  let dyn     ← (Parser.run fixtureBytes
                    (parseTable initArrEnd 0xc0)).toOption
  let symtab  ← (Parser.run fixtureBytes
                    (decodeArray (α := RawSym) strtabEnd 2)).toOption
  let rela    ← (Parser.run fixtureBytes
                    (decodeArray (α := RawRela) hashEnd 1)).toOption
  let initArr ← (Parser.run fixtureBytes
                    (decodeArray (α := UInt64) relaEnd 1)).toOption
  return {
    header,
    phdrs,
    strtab  := fixtureBytes.extract phdrsEnd strtabEnd,
    symtab,
    needed  := (findAll dyn DT_NEEDED).map (·.d_un),
    soname  := val? dyn DT_SONAME,
    runpath := val? dyn DT_RUNPATH,
    rela,
    jmprel  := #[],
    initArr,
    finiArr := #[] }

-- ---- Cross-section coordination `#guard`s ────────────────────────────
-- Per-struct field decoding is checked standalone in each Raw*.lean.
-- Here we verify the multi-section invariants the fixture is engineered
-- to satisfy.

#guard match fixture with
  | some r =>
       r.header.e_phnum.toNat == r.phdrs.size                -- ehdr.phnum ↔ phdrs.size
    && r.symtab.size == 2                                    -- DT_HASH.nchain ↔ symtab entries
    && r.needed == #[1]                                      -- one DT_NEEDED → strtab[0x01]
    && r.soname == some 0x12                                 -- DT_SONAME → strtab[0x12]
    && r.runpath == some 0x1b                                -- DT_RUNPATH → strtab[0x1b]
    && r.rela.size == 1
    && r.initArr.size == 1
  | none   => false

-- `vaToOffset` is the identity on this fixture (PT_LOAD vaddr = offset).
#guard match fixture with
  | some r =>
       vaToOffset r.phdrs 0x0b0 == some 0xb0    -- strtab vaddr (DT_STRTAB)
    && vaToOffset r.phdrs 0x100 == some 0x100   -- hash vaddr / e_entry
    && vaToOffset r.phdrs 0x1e7 == some 0x1e7   -- last covered byte
    && vaToOffset r.phdrs 0x1e8 == none         -- one past the end
  | none   => false

end Example

end LeanLoad.Parse.RawElf

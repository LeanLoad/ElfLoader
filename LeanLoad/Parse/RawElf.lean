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

Raw types live in `Parse.Raw{Ehdr,Strtab,Sym,Rela,Phdr,Dyn,Hash}`.
The `.dynamic` array's variable-length parser and by-tag lookups
share a file with the `RawDyn` struct (`Parse.RawDyn`); the
`DynInfo` projection (`.dynamic` resolved into one record of vaddr
pointers + size pairs) lives in `Parse.DynInfo`.

`parse` is monad-polymorphic over a `FileReader m` (see
`Parse/Reader.lean`):

  • Production — `FileReader IO` backed by `Runtime.pread`. The
    public `parse : FileHandle → IO RawElf` is a thin wrapper.

  • Fixture — `FileReader Id` over an in-memory `ByteArray`. The
    same `parseM` runs over the hand-crafted bytes downstream of
    every per-struct `Raw*.fixtureBytes`. There is no parallel
    walker; `fixture` *is* `parseM (pureReader fixtureBytes)`.
-/

import LeanLoad.Parse.Decode
import LeanLoad.Parse.Reader
import LeanLoad.Parse.Header.Ehdr
import LeanLoad.Parse.Dynamic.RawStrtab
import LeanLoad.Parse.Dynamic.RawSym
import LeanLoad.Parse.Dynamic.RawRela
import LeanLoad.Parse.Header.Phdr
import LeanLoad.Parse.Dynamic.RawDyn
import LeanLoad.Parse.Dynamic.RawHash
import LeanLoad.Parse.Dynamic.DynInfo
import LeanLoad.Runtime

namespace LeanLoad.Parse

-- ============================================================================
-- RawElf — output of `parse`. Bytes decoded only; no witnesses.
--
-- The phdr-array helper `vaToOffset` (virtual-address ↔ file-offset
-- translation, used below by `parseAtVa`) lives with the type it
-- operates on, in `Parse/Header/Phdr.lean`.
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
  symtab  : RawSymtab
  /-- `DT_NEEDED` strtab byte-offsets, in dynamic-array order. -/
  needed  : Array StrtabOff
  /-- `DT_SONAME` strtab byte-offset, if present. -/
  soname  : Option StrtabOff
  /-- `DT_RUNPATH` strtab byte-offset, if present. `DT_RPATH` is
      **not** consulted (gabi 08 deprecates it; Discover refuses
      it too). A DT_RPATH-only object yields `none`. -/
  runpath : Option StrtabOff
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

-- ============================================================================
-- Vaddr-aware reader helpers — phdr-routed counterparts of `parseAt`
-- from `Parse/Reader.lean`. They live here (not in `Reader.lean`)
-- because vaddr→offset translation is ELF-specific (`vaToOffset` over
-- a `RawPhdr` array). All three are monad-polymorphic over the reader.
-- ============================================================================

/-- Resolve `va` to a file offset via `vaToOffset` over PT_LOAD
    coverage, then defer to `parseAt`. Throws if no PT_LOAD covers
    `va`. The vaddr is typed `Vaddr` — a raw file offset cannot be
    passed by mistake. -/
def parseAtVa [Monad m] (r : FileReader m) (phdrs : Array RawPhdr)
    (va : Vaddr) (len : UInt64) (parser : Parser α) : ExceptT String m α :=
  match vaToOffset phdrs va with
  | some off => parseAt r off.toUInt64 len parser
  | none     => throw s!"va 0x{va.toNat} not in any PT_LOAD"

/-- Workhorse for vaddr-routed fixed-size tables. Reads `count`
    entries of `entrySize` bytes each, starting at `va`. Each entry
    is decoded via the `BytesDecode α` instance. -/
def parseArrayAtVa [Monad m] [BytesDecode α]
    (r : FileReader m) (phdrs : Array RawPhdr)
    (entrySize : Nat) (va : Vaddr) (count : Nat) : ExceptT String m (Array α) :=
  parseAtVa r phdrs va (count * entrySize).toUInt64
    (decodeArray (α := α) 0 count)

/-- Read a gabi-08 `(DT_X, DT_XSZ)`-keyed sized table. `loc` is the
    `(vaddr, size)` pair already projected out of `DynInfo`; `none`
    yields an empty array (tag absent in `.dynamic`). Entry count
    derives from `size / entrySize`. -/
def parseSized [Monad m] [BytesDecode α]
    (r : FileReader m) (phdrs : Array RawPhdr) (entrySize : Nat)
    (loc : Option (Vaddr × UInt64)) : ExceptT String m (Array α) :=
  match loc with
  | none       => pure #[]
  | some (v,s) => parseArrayAtVa r phdrs entrySize v (s.toNat / entrySize)

-- ============================================================================
-- Layer 3 read helpers — one per section whose read isn't already a
-- one-liner `parseSized`. Lifting these out of `parseM` keeps Layer 3
-- a flat list-of-sections; each helper documents one section's read
-- contract independently.
-- ============================================================================

/-- Read `DT_HASH`'s `nchain` field — the authoritative count for
    the dynamic symbol table (the only section whose size doesn't
    pair with a `DT_*SZ` tag). Returns `0` if `DT_HASH` is absent;
    `--hash-style=both` in the build ensures it's present. -/
def readSymCount [Monad m] (r : FileReader m) (phdrs : Array RawPhdr)
    (hashVa : Option Vaddr) : ExceptT String m Nat := do
  match hashVa with
  | none    => pure 0
  | some va =>
      let hdr ← parseAtVa r phdrs va RawHashSize.toUInt64
                  (BytesDecode.decode : Parser RawHash)
      pure hdr.nchain.toNat

/-- Read the dynamic string table (`.dynstr`) as a raw `ByteArray`.
    Empty if `DT_STRTAB` is absent. UTF-8 decoding lives in
    `RawStrtab.lookup`. -/
def readStrtab [Monad m] (r : FileReader m) (phdrs : Array RawPhdr)
    (loc : Option (Vaddr × UInt64)) : ExceptT String m RawStrtab :=
  match loc with
  | none       => pure (ByteArray.mk #[])
  | some (v,s) => parseAtVa r phdrs v s buffer

/-- Read the dynamic symbol table. Returns empty if `DT_SYMTAB` is
    absent or `count` is 0 (e.g., missing `DT_HASH`). -/
def readSymtab [Monad m] (r : FileReader m) (phdrs : Array RawPhdr)
    (symVa : Option Vaddr) (count : Nat) : ExceptT String m RawSymtab := do
  if count == 0 then return #[]
  match symVa with
  | none    => pure #[]
  | some va => parseArrayAtVa r phdrs RawSymSize va count

-- ============================================================================
-- Three-stage parse pipeline. Each stage has a named function and a
-- typed intermediate; `parseM` is the assembly.
--
--   Stage 1: `parseHeaders` — file-offset reads chained off the ELF
--     header. Produces `RawHeaders`. Offsets come from `ehdr`'s fields
--     or `PT_DYNAMIC`'s `p_offset` directly — no PT_LOAD navigation.
--
--   Stage 2: `DynInfo.ofTable` — pure projection of `.dynamic` into
--     a record of section-locating pointers. Lives in `DynInfo.lean`.
--
--   Stage 3: `fetchDynContents` — vaddr-keyed reads via `DynInfo`
--     fields. Produces `DynContents`. Each vaddr is routed through
--     `parseAtVa` over PT_LOAD coverage.
--
-- Both intermediate types (`RawHeaders`, `DynContents`) are local to
-- this file — `RawElf` stays flat for downstream consumers.
-- ============================================================================

/-- Output of stage 1. Bundles the three file-offset-keyed reads. -/
private structure RawHeaders where
  header : RawEhdr
  phdrs  : Array RawPhdr
  dyn    : RawDyntab

/-- Output of stage 3. Bundles the six vaddr-keyed section reads.
    Field types are concrete and already exist — this is just a
    function-result carrier, not a new semantic concept. -/
private structure DynContents where
  strtab  : RawStrtab
  symtab  : RawSymtab
  rela    : Array RawRela
  jmprel  : Array RawRela
  initArr : Array UInt64
  finiArr : Array UInt64

/-- Stage 1: read everything addressable by direct file offsets —
    `ehdr` (offset 0), the phdr table (`ehdr.e_phoff`), and the
    `.dynamic` array (`PT_DYNAMIC.p_offset`). No PT_LOAD navigation. -/
def parseHeaders [Monad m] (r : FileReader m) : ExceptT String m RawHeaders := do
  let header ← parseAt r 0 RawEhdrSize.toUInt64
                 (BytesDecode.decode : Parser RawEhdr)
  let phdrs ← parseAt r header.e_phoff
                (header.e_phnum.toNat * RawPhdrSize).toUInt64
                (decodeArray (α := RawPhdr) 0 header.e_phnum.toNat)
  let dyn ← match phdrs.find? (·.p_type == PT_DYNAMIC) with
    | none    => pure #[]
    | some ph => parseAt r ph.p_offset ph.p_filesz
                   (RawDyntab.parseTable 0 ph.p_filesz.toNat)
  return { header, phdrs, dyn }

/-- Stage 3: read every section pointed at by `DynInfo`, routing each
    vaddr through `vaToOffset` over `phdrs`' PT_LOAD coverage. Per-
    section helpers (`readSymCount`/`readStrtab`/`readSymtab`/
    `parseSized`) handle the absent-tag fallbacks. -/
def fetchDynContents [Monad m] (r : FileReader m)
    (phdrs : Array RawPhdr) (info : DynInfo) : ExceptT String m DynContents := do
  let symCount ← readSymCount r phdrs info.hash
  let strtab   ← readStrtab   r phdrs info.strtab
  let symtab   ← readSymtab   r phdrs info.symtab symCount
  let rela     ← parseSized   r phdrs RawRelaSize info.rela
  let jmprel   ← parseSized   r phdrs RawRelaSize info.jmprel
  let initArr  ← parseSized   r phdrs 8           info.initArr
  let finiArr  ← parseSized   r phdrs 8           info.finiArr
  return { strtab, symtab, rela, jmprel, initArr, finiArr }

/-- Monad-polymorphic byte-parse of an ELF — assembly of the three
    stages. The `FileReader m` abstracts how bytes arrive (kernel
    `pread` in production, slice of an in-memory `ByteArray` in the
    fixture). Errors flow as `ExceptT String m`. -/
def parseM [Monad m] (r : FileReader m) : ExceptT String m RawElf := do
  let h ← parseHeaders r
  let info := DynInfo.ofTable h.dyn
  let c ← fetchDynContents r h.phdrs info
  return {
    header  := h.header,
    phdrs   := h.phdrs,
    strtab  := c.strtab,
    symtab  := c.symtab,
    needed  := info.needed,
    soname  := info.soname,
    runpath := info.runpath,
    rela    := c.rela,
    jmprel  := c.jmprel,
    initArr := c.initArr,
    finiArr := c.finiArr
  }

/-- Production entry point: parse the ELF behind an open kernel
    `FileHandle` via per-section `pread`s. Each section's bytes live
    in their own small `ByteArray` and are GC'd after parsing — no
    whole-file `ByteArray` is ever constructed. -/
def parse (h : Runtime.FileHandle) : IO RawElf := do
  match ← (parseM (Runtime.fileReader h)).run with
  | .ok r    => pure r
  | .error e => throw (IO.userError s!"parse: {e}")

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
-- entry count, and so on.
--
-- Crucially, the fixture exercises *the same `parseM`* that
-- production uses — only the `FileReader` instance changes (`pureReader`
-- vs `Runtime.fileReader`). Section offsets are no longer hand-walked
-- here; `parseM` discovers them via `vaToOffset` over the parsed phdrs.
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
-- arrays read inline by `parseM`'s `RawHash` decode / `parseSized`),
-- so they live inline here.

-- Hash section (8 bytes): `nbucket = 1`, `nchain = 2`. `parseM` reads
-- only the first 8 bytes via the `RawHash` decoder; the bucket/chain
-- arrays a real ELF appends are unused by LeanLoad and omitted.
private def hashBytes : ByteArray := ⟨#[
  0x01, 0x00, 0x00, 0x00,                                       -- nbucket = 1
  0x02, 0x00, 0x00, 0x00                                        -- nchain  = 2
]⟩

-- Init array (8 bytes): one ctor pointer at 0x100 (inside PT_LOAD's
-- executable memsz, so `initArrInExecSeg` accepts at elaborate time).
private def initArrBytes : ByteArray := ⟨#[
  0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
]⟩

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
    ++ RawDyntab.fixtureBytes

-- Total size: sum of each section's `fixtureBytes`.
#guard fixtureBytes.size = 0x1e8                  -- 488 bytes total

/-- Parse-side counterpart to `Parse.RawElf.parse`, but pure: built by
    running the same `parseM` over a `pureReader` of `fixtureBytes`.
    Returns `Except String RawElf` — the same error channel production
    surfaces, just without IO wrapping.

    This is what `LeanLoad/Example.lean` runs through `elaborate` for
    the real-world acceptance check at the parse → elaborate boundary. -/
def fixture : Except String RawElf :=
  (parseM (pureReader fixtureBytes)).run

-- ---- Cross-section coordination `#guard`s ────────────────────────────
-- Per-struct field decoding is checked standalone in each Raw*.lean.
-- Here we verify the multi-section invariants the fixture is engineered
-- to satisfy — and, because `fixture` calls the *production* `parseM`,
-- these guards also exercise that production code on a synthetic ELF.

#guard match fixture with
  | .ok r =>
       r.header.e_phnum.toNat == r.phdrs.size                       -- ehdr.phnum ↔ phdrs.size
    && r.symtab.size == 2                                           -- DT_HASH.nchain ↔ symtab entries
    && r.needed == #[(1 : StrtabOff)]                               -- one DT_NEEDED → strtab[0x01]
    && r.soname == some (0x12 : StrtabOff)                          -- DT_SONAME → strtab[0x12]
    && r.runpath == some (0x1b : StrtabOff)                         -- DT_RUNPATH → strtab[0x1b]
    && r.rela.size == 1
    && r.initArr.size == 1
  | .error _ => false

-- `vaToOffset` is the identity on this fixture (PT_LOAD vaddr = offset).
#guard match fixture with
  | .ok r =>
       vaToOffset r.phdrs (0x0b0 : Vaddr) == some 0xb0    -- strtab vaddr (DT_STRTAB)
    && vaToOffset r.phdrs (0x100 : Vaddr) == some 0x100   -- hash vaddr / e_entry
    && vaToOffset r.phdrs (0x1e7 : Vaddr) == some 0x1e7   -- last covered byte
    && vaToOffset r.phdrs (0x1e8 : Vaddr) == none         -- one past the end
  | .error _ => false

end Example

end LeanLoad.Parse.RawElf

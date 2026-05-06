/-
Aggregate ELF parser: walks an entire ELF the way a loader needs to —
header → program headers → `.dynamic` → string table → dynamic symbol
table → relocation tables → `DT_NEEDED` strings → init/fini lists.

The dynamic symbol-table count is taken from `DT_HASH`'s `nchain`
field (gabi 08 § Hash Table) when present, falling back to walking
`DT_GNU_HASH`'s chain table when only the GNU extension is emitted
(gnu-gabi `program-loading-and-dynamic-linking.txt` § Hashes). Modern
Linux toolchains default to gnu-only.

Spec types live in `LeanLoad.Spec.{Header,Program,Dynamic,Symbol,Reloc}`;
this file just glues their parsers together into a `ParsedElf`.
-/

import LeanLoad.Parse.Bytes
import LeanLoad.Parse.Header
import LeanLoad.Parse.Program
import LeanLoad.Parse.Dynamic
import LeanLoad.Parse.StringTable
import LeanLoad.Parse.Symbol
import LeanLoad.Parse.Reloc
import LeanLoad.Parse.GnuHash
import LeanLoad.Runtime

namespace LeanLoad.Parse.File

open LeanLoad
open LeanLoad.Parse.Bytes

-- ============================================================================
-- Virtual-address ↔ file-offset translation
-- ============================================================================

/-- Translate a virtual address to a file offset by walking the
    `PT_LOAD` segments. Returns `none` if no `PT_LOAD` covers the
    address. -/
def vaToOffset (phdrs : Array Spec.Program.Header64) (va : UInt64) : Option Nat :=
  phdrs.findSome? fun ph =>
    if ph.p_type == Spec.Program.PT_LOAD
       && ph.p_vaddr ≤ va
       && va < ph.p_vaddr + ph.p_memsz then
      some ((va - ph.p_vaddr).toNat + ph.p_offset.toNat)
    else
      none

section UnitTest
-- A two-segment ELF: [.text @va 0x1000, file 0x1000, len 0x1000]
-- and [.data @va 0x3000, file 0x2000, len 0x500]. Soundness is
-- proved by `Thm.vaToOffset_correct`; these spot-check the formula.
private def phdrs : Array Spec.Program.Header64 := #[
  { (default : Spec.Program.Header64) with
    p_type := Spec.Program.PT_LOAD,
    p_vaddr := 0x1000, p_memsz := 0x1000,
    p_offset := 0x1000, p_filesz := 0x1000 },
  { (default : Spec.Program.Header64) with
    p_type := Spec.Program.PT_LOAD,
    p_vaddr := 0x3000, p_memsz := 0x500,
    p_offset := 0x2000, p_filesz := 0x500 } ]

#guard vaToOffset phdrs 0x1000 = some 0x1000   -- start of .text
#guard vaToOffset phdrs 0x1abc = some 0x1abc   -- mid .text
#guard vaToOffset phdrs 0x3010 = some 0x2010   -- mid .data (different file offset)
#guard vaToOffset phdrs 0x0fff = none           -- before .text
#guard vaToOffset phdrs 0x2500 = none           -- gap between segments
#guard vaToOffset phdrs 0x3500 = none           -- past .data
end UnitTest

-- ============================================================================
-- Aggregated parse result (project-defined; not gabi)
-- ============================================================================

/-- Everything the loader needs that comes from parsing a single ELF. -/
structure ParsedElf where
  header  : Spec.Header.ElfHeader64
  phdrs   : Array Spec.Program.Header64
  /-- The `.dynamic` array, empty if no `PT_DYNAMIC`. -/
  dyn     : Array Spec.Dynamic.Dyn64
  /-- The dynamic string table (`DT_STRTAB`), empty if absent. -/
  strtab  : Spec.StringTable.StringTable
  /-- Dynamic symbol table (`DT_SYMTAB`), sized via `DT_HASH`'s
      `nchain`. Empty if neither is present. -/
  symtab  : Array Spec.Symbol.Symbol64
  /-- Resolved `DT_NEEDED` strings, in dynamic-array order. -/
  needed  : Array String
  /-- `DT_SONAME` if present (the canonical name of this object). -/
  soname  : Option String
  /-- `DT_RUNPATH` (gabi 08; deprecated `DT_RPATH` falls back to this). -/
  runpath : Option String
  /-- General `Rela` relocations from `DT_RELA`. -/
  rela    : Array Spec.Reloc.Rela64
  /-- PLT relocations from `DT_JMPREL` (only `Rela` form supported). -/
  jmprel  : Array Spec.Reloc.Rela64
  /-- `DT_INIT_ARRAY` entries — already parsed from the file bytes. For
      `ET_DYN`, each entry is a relative address; the runtime adds the
      chosen base. For `ET_EXEC`, entries are absolute. (gabi 08 also
      defines `DT_INIT`, `DT_FINI`, `DT_FINI_ARRAY`, `DT_PREINIT_ARRAY`;
      none are consumed by the loader yet — added back when needed.) -/
  initArr : Array UInt64
  deriving Inhabited

-- ============================================================================
-- Helpers for reading from a `.dynamic` array
-- ============================================================================

private def dynVal? (dyn : Array Spec.Dynamic.Dyn64) (tag : UInt64) : Option UInt64 :=
  (Parse.Dynamic.find? dyn tag).map (·.d_un)

private def dynPair? (dyn : Array Spec.Dynamic.Dyn64) (tagA tagB : UInt64) : Option (UInt64 × UInt64) := do
  let a ← dynVal? dyn tagA
  let b ← dynVal? dyn tagB
  return (a, b)

/-- Find the `PT_LOAD` whose file range covers `off`. Used to upper-
    bound `DT_GNU_HASH`'s chain (no size field in the dynamic table). -/
private def containingPTLoad (phdrs : Array Spec.Program.Header64) (off : Nat)
    : Option Spec.Program.Header64 :=
  phdrs.find? fun ph =>
    ph.p_type == Spec.Program.PT_LOAD &&
    ph.p_offset.toNat ≤ off &&
    off < ph.p_offset.toNat + ph.p_filesz.toNat

/-- `pread` `len` bytes at `offset` and run `parser` from the start.
    Each section's parsers take an `offset` parameter that becomes 0
    here (we already preadʼd from the file at the right place). -/
private def parseSection {α} (h : Runtime.FileHandle) (label : String)
    (offset : UInt64) (len : USize) (parser : Parser α) : IO α := do
  let bytes ← Runtime.pread h offset len
  match Parser.run bytes parser with
  | .ok v    => pure v
  | .error e => throw (IO.userError s!"parse {label}: {e}")

/-- Resolve `vaddr` to a file offset; throw if no `PT_LOAD` covers it. -/
private def vaToOffsetIO (phdrs : Array Spec.Program.Header64) (label : String)
    (vaddr : UInt64) : IO Nat :=
  match vaToOffset phdrs vaddr with
  | some off => pure off
  | none     => throw (IO.userError s!"parse {label}: va 0x{vaddr.toNat} not in any PT_LOAD")

-- ============================================================================
-- Top-level parser — `pread`-driven, one section per syscall.
-- ============================================================================

/-- Parse an ELF file via per-section `pread`s on a `FileHandle`.
    Each section's bytes live in their own small `ByteArray` and are
    GC'd after parsing — no whole-file `ByteArray` is constructed. -/
def parse (h : Runtime.FileHandle) : IO ParsedElf := do
  -- ELF header (64 bytes).
  -- ELF header is fixed-size (gabi 02 Elf64_Ehdr: 64 bytes).
  let header ← parseSection h "header" 0 64 Parse.Header.parse

  -- Phdr table (e_phnum × 56 bytes).
  let phdrTableSize := (header.e_phnum.toNat * Spec.Program.entrySize).toUSize
  let phdrs ← parseSection h "phdrs" header.e_phoff phdrTableSize
                (Parse.Program.parseTable 0 header.e_phnum.toNat)

  -- PT_DYNAMIC (sized by `p_filesz`).
  let dyn ← match phdrs.find? (·.p_type == Spec.Program.PT_DYNAMIC) with
    | none    => pure #[]
    | some ph =>
      parseSection h "dynamic" ph.p_offset ph.p_filesz.toNat.toUSize
        (Parse.Dynamic.parseTable 0 ph.p_filesz.toNat)

  -- DT_STRTAB (sized by DT_STRSZ).
  let strtab ← match dynPair? dyn Spec.Dynamic.DT_STRTAB Spec.Dynamic.DT_STRSZ with
    | none             => pure (ByteArray.mk #[])
    | some (vaddr, sz) =>
      let off ← vaToOffsetIO phdrs "DT_STRTAB" vaddr
      parseSection h "DT_STRTAB" off.toUInt64 sz.toNat.toUSize
        (Parse.StringTable.parse 0 sz.toNat)

  -- Symbol count (from DT_HASH's nchain or by walking DT_GNU_HASH's chain).
  let symCount : Nat ←
    match dynVal? dyn Spec.Dynamic.DT_HASH, dynVal? dyn Spec.Dynamic.DT_GNU_HASH with
    | some hashVa, _ =>
      let off ← vaToOffsetIO phdrs "DT_HASH" hashVa
      -- Need only the 8-byte (nbucket, nchain) header.
      parseSection h "DT_HASH" off.toUInt64 8
        (do let _ ← Bytes.u32le; let nchain ← Bytes.u32le; return nchain.toNat)
    | none, some gnuHashVa =>
      let off ← vaToOffsetIO phdrs "DT_GNU_HASH" gnuHashVa
      -- Chain extends until end of containing PT_LOAD; pread that tail.
      match containingPTLoad phdrs off with
      | none    => throw (IO.userError s!"parse DT_GNU_HASH: offset 0x{off} in no PT_LOAD")
      | some ph =>
        let segEnd  := ph.p_offset.toNat + ph.p_filesz.toNat
        let availLen := (segEnd - off).toUSize
        parseSection h "DT_GNU_HASH" off.toUInt64 availLen
          (Parse.GnuHash.parseSymCount 0)
    | none, none => pure 0

  -- DT_SYMTAB (sized by `symCount × Symbol64.entrySize`).
  let symtab ← if symCount == 0 then pure #[]
    else match dynVal? dyn Spec.Dynamic.DT_SYMTAB with
      | none       => pure #[]
      | some vaddr =>
        let off := ← vaToOffsetIO phdrs "DT_SYMTAB" vaddr
        let symSize := (symCount * Spec.Symbol.entrySize).toUSize
        parseSection h "DT_SYMTAB" off.toUInt64 symSize
          (Parse.Symbol.parseTable 0 symCount)

  let neededOffsets := (Parse.Dynamic.findAll dyn Spec.Dynamic.DT_NEEDED).map (·.d_un)
  let needed := neededOffsets.filterMap (fun off => Spec.StringTable.lookup strtab off.toNat)

  let lookupStr (tag : UInt64) : Option String :=
    (dynVal? dyn tag).bind (fun off => Spec.StringTable.lookup strtab off.toNat)
  let soname  := lookupStr Spec.Dynamic.DT_SONAME
  let runpath := lookupStr Spec.Dynamic.DT_RUNPATH <|> lookupStr Spec.Dynamic.DT_RPATH

  -- DT_RELA / DT_JMPREL (sized by their respective `*SZ`).
  let parseRelaPair (tagAddr tagSz : UInt64) (label : String) : IO (Array Spec.Reloc.Rela64) := do
    match dynPair? dyn tagAddr tagSz with
    | none             => pure #[]
    | some (vaddr, sz) =>
      let off ← vaToOffsetIO phdrs label vaddr
      let count := sz.toNat / Spec.Reloc.Rela64.entrySize
      parseSection h label off.toUInt64 sz.toNat.toUSize
        (Parse.Reloc.parseRelaTable 0 count)
  let rela   ← parseRelaPair Spec.Dynamic.DT_RELA   Spec.Dynamic.DT_RELASZ   "DT_RELA"
  let jmprel ← parseRelaPair Spec.Dynamic.DT_JMPREL Spec.Dynamic.DT_PLTRELSZ "DT_JMPREL"

  -- DT_INIT_ARRAY (sized by DT_INIT_ARRAYSZ).
  let initArr ← match dynPair? dyn Spec.Dynamic.DT_INIT_ARRAY Spec.Dynamic.DT_INIT_ARRAYSZ with
    | none             => pure #[]
    | some (vaddr, sz) =>
      let off ← vaToOffsetIO phdrs "DT_INIT_ARRAY" vaddr
      let count := sz.toNat / 8
      parseSection h "DT_INIT_ARRAY" off.toUInt64 sz.toNat.toUSize
        (Bytes.parseArray 0 count Bytes.u64le)

  return {
    header, phdrs, dyn, strtab, symtab, needed, soname, runpath,
    rela, jmprel, initArr
  }

-- ============================================================================
-- IO test runner. Parses the given bytes (typically `build/main`) and
-- asserts the header + DT_NEEDED look reasonable for our musl-built
-- example. Aggregated by `LeanLoad.Test`.
-- ============================================================================

/-- End-to-end smoke test: parse via FileHandle and assert basics. -/
def test (h : Runtime.FileHandle) : IO Nat := do
  let mut failures := 0
  try
    let elf ← parse h
    if elf.header.e_type != Spec.Header.ET_DYN then
      IO.eprintln s!"e_type: expected ET_DYN={Spec.Header.ET_DYN}, got {elf.header.e_type}"
      failures := failures + 1
    if elf.header.e_ehsize != 64 then
      IO.eprintln s!"e_ehsize: expected 64, got {elf.header.e_ehsize}"
      failures := failures + 1
    if elf.header.e_phentsize != 56 then
      IO.eprintln s!"e_phentsize: expected 56, got {elf.header.e_phentsize}"
      failures := failures + 1
    if elf.phdrs.size != elf.header.e_phnum.toNat then
      IO.eprintln s!"phnum mismatch: header says {elf.header.e_phnum}, parsed {elf.phdrs.size}"
      failures := failures + 1
    if elf.needed.size < 3 then
      IO.eprintln s!"expected ≥ 3 NEEDED entries, got {elf.needed.size}: {elf.needed}"
      failures := failures + 1
    if !elf.needed.any (· == "libfoo.so") then
      IO.eprintln s!"libfoo.so not in NEEDED: {elf.needed}"
      failures := failures + 1
    if !elf.needed.any (· == "libbar.so") then
      IO.eprintln s!"libbar.so not in NEEDED: {elf.needed}"
      failures := failures + 1
    if elf.runpath.isNone then
      IO.eprintln "expected DT_RUNPATH set"
      failures := failures + 1
  catch e =>
    IO.eprintln s!"File.parse failed: {e}"
    failures := failures + 1
  return failures

end LeanLoad.Parse.File

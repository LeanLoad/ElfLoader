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
import LeanLoad.Spec.GnuHash

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

-- ============================================================================
-- Aggregated parse result (project-defined; not gabi)
-- ============================================================================

/-- Everything the loader needs that comes from parsing a single ELF. -/
structure ParsedElf where
  bytes   : ByteArray
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
  /-- Address of `DT_INIT`, if present. -/
  initFn  : Option UInt64
  /-- Address of `DT_FINI`, if present. -/
  finiFn  : Option UInt64
  /-- `DT_INIT_ARRAY` entries — already parsed from the file bytes. For
      `ET_DYN`, each entry is a relative address; the runtime adds the
      chosen base. For `ET_EXEC`, entries are absolute. -/
  initArr : Array UInt64
  /-- `DT_FINI_ARRAY` entries, same convention as `initArr`. -/
  finiArr : Array UInt64
  /-- `DT_PREINIT_ARRAY` entries, same convention. -/
  preinitArr : Array UInt64
  deriving Inhabited

-- ============================================================================
-- Helpers for reading from a `.dynamic` array
-- ============================================================================

private def dynVal? (dyn : Array Spec.Dynamic.Dyn64) (tag : UInt64) : Option UInt64 :=
  (Spec.Dynamic.find? dyn tag).map (·.d_un)

private def dynPair? (dyn : Array Spec.Dynamic.Dyn64) (tagA tagB : UInt64) : Option (UInt64 × UInt64) := do
  let a ← dynVal? dyn tagA
  let b ← dynVal? dyn tagB
  return (a, b)

private def vaOffsetOrThrow (phdrs : Array Spec.Program.Header64) (tag : String) (vaddr : UInt64)
    : Except String Nat :=
  match vaToOffset phdrs vaddr with
  | some off => .ok off
  | none     => .error s!"{tag} va 0x{vaddr.toNat} not in PT_LOAD"

private def parseAtDyn (phdrs : Array Spec.Program.Header64) (bytes : ByteArray)
    (tag : String) (vaddr? : Option UInt64) (default : α) (p : Nat → Parser α)
    : Except String α :=
  match vaddr? with
  | none       => .ok default
  | some vaddr => do
    let off ← vaOffsetOrThrow phdrs tag vaddr
    Parser.run bytes (p off)

-- ============================================================================
-- Symbol count from `DT_GNU_HASH`. Layout is gnu-gabi § Hashes; the
-- count derivation is `Spec.GnuHash.symCount` (see that module for
-- the linker invariant we rely on, since gnu-gabi defines no count
-- tag and the algorithm itself is community lore).
-- ============================================================================

/-- Read a GNU hash table at file offset `off` and return the dynsym
    count via `Spec.GnuHash.symCount`. Reads buckets exactly, then
    reads chain entries up to the end of the byte buffer (the chain's
    real length is unbounded by the table itself; the caller's file
    size is the only natural upper bound). -/
private def parseGnuHashSymCount (off : Nat) : Parser Nat := do
  Bytes.seek off
  let nbuckets   := (← Bytes.u32le).toNat
  let symoffset  := (← Bytes.u32le).toNat
  let bloomWords := (← Bytes.u32le).toNat
  let _bloomShift ← Bytes.u32le
  Bytes.skip (bloomWords * 8)  -- ELF64: each bloom word is 64 bits
  let mut buckets : Array UInt32 := Array.mkEmpty nbuckets
  for _ in [:nbuckets] do
    buckets := buckets.push (← Bytes.u32le)
  let s ← get
  let chainBound := (s.bytes.size - s.pos) / 4
  let mut chain : Array UInt32 := Array.mkEmpty chainBound
  for _ in [:chainBound] do
    chain := chain.push (← Bytes.u32le)
  match Spec.GnuHash.symCount symoffset buckets chain with
  | some n => return n
  | none   => throw "parseGnuHashSymCount: chain has no end marker (malformed)"

-- ============================================================================
-- Top-level parser
-- ============================================================================

/-- Parse an entire ELF file into a `ParsedElf`. -/
def parse (bytes : ByteArray) : Except String ParsedElf := do
  let header ← Parser.run bytes Parse.Header.parse
  let phdrs  ← Parser.run bytes
                 (Parse.Program.parseTable header.e_phoff.toNat header.e_phnum.toNat)

  let dyn ← match phdrs.find? (·.p_type == Spec.Program.PT_DYNAMIC) with
            | none    => pure #[]
            | some ph => Parser.run bytes
                          (Parse.Dynamic.parseTable ph.p_offset.toNat ph.p_filesz.toNat)

  let strtab ← match dynPair? dyn Spec.Dynamic.DT_STRTAB Spec.Dynamic.DT_STRSZ with
    | none             => pure (ByteArray.mk #[])
    | some (vaddr, sz) =>
      parseAtDyn phdrs bytes "DT_STRTAB" (some vaddr) (ByteArray.mk #[])
        (fun off => Parse.StringTable.parse off sz.toNat)

  let symCount : Nat ←
    match dynVal? dyn Spec.Dynamic.DT_HASH, dynVal? dyn Spec.Dynamic.DT_GNU_HASH with
    | some _, _ =>
      parseAtDyn phdrs bytes "DT_HASH" (dynVal? dyn Spec.Dynamic.DT_HASH) 0
        (fun off => do
          let nchain ← Bytes.atOffset (off + 4) Bytes.u32le
          return nchain.toNat)
    | none, some _ =>
      parseAtDyn phdrs bytes "DT_GNU_HASH"
        (dynVal? dyn Spec.Dynamic.DT_GNU_HASH) 0 parseGnuHashSymCount
    | none, none => pure 0

  let symtab ←
    if symCount == 0 then pure #[]
    else parseAtDyn phdrs bytes "DT_SYMTAB" (dynVal? dyn Spec.Dynamic.DT_SYMTAB) #[]
           (fun off => Parse.Symbol.parseTable off symCount)

  let neededOffsets := (Spec.Dynamic.findAll dyn Spec.Dynamic.DT_NEEDED).map (·.d_un)
  let needed := neededOffsets.filterMap (fun off => Spec.StringTable.lookup strtab off.toNat)

  let lookupStr (tag : UInt64) : Option String :=
    (dynVal? dyn tag).bind (fun off => Spec.StringTable.lookup strtab off.toNat)
  let soname  := lookupStr Spec.Dynamic.DT_SONAME
  let runpath := lookupStr Spec.Dynamic.DT_RUNPATH <|> lookupStr Spec.Dynamic.DT_RPATH

  let parseRelaPair (tagAddr tagSz : UInt64) (label : String)
      : Except String (Array Spec.Reloc.Rela64) :=
    match dynPair? dyn tagAddr tagSz with
    | none             => .ok #[]
    | some (vaddr, sz) =>
      let count := sz.toNat / Spec.Reloc.Rela64.entrySize
      parseAtDyn phdrs bytes label (some vaddr) #[]
        (fun off => Parse.Reloc.parseRelaTable off count)
  let rela   ← parseRelaPair Spec.Dynamic.DT_RELA   Spec.Dynamic.DT_RELASZ   "DT_RELA"
  let jmprel ← parseRelaPair Spec.Dynamic.DT_JMPREL Spec.Dynamic.DT_PLTRELSZ "DT_JMPREL"

  let initFn := dynVal? dyn Spec.Dynamic.DT_INIT
  let finiFn := dynVal? dyn Spec.Dynamic.DT_FINI
  let parseFnArray (tagAddr tagSz : UInt64) (label : String)
      : Except String (Array UInt64) :=
    match dynPair? dyn tagAddr tagSz with
    | none           => .ok #[]
    | some (vaddr, sz) =>
      let count := sz.toNat / 8
      parseAtDyn phdrs bytes label (some vaddr) #[]
        (fun off => Bytes.parseArray off count Bytes.u64le)
  let initArr    ← parseFnArray Spec.Dynamic.DT_INIT_ARRAY    Spec.Dynamic.DT_INIT_ARRAYSZ    "DT_INIT_ARRAY"
  let finiArr    ← parseFnArray Spec.Dynamic.DT_FINI_ARRAY    Spec.Dynamic.DT_FINI_ARRAYSZ    "DT_FINI_ARRAY"
  let preinitArr ← parseFnArray Spec.Dynamic.DT_PREINIT_ARRAY Spec.Dynamic.DT_PREINIT_ARRAYSZ "DT_PREINIT_ARRAY"

  return {
    bytes, header, phdrs, dyn, strtab, symtab, needed, soname, runpath,
    rela, jmprel, initFn, finiFn, initArr, finiArr, preinitArr
  }

end LeanLoad.Parse.File

-- ============================================================================
-- IO test runner. Parses the given bytes (typically `build/main`) and
-- asserts the header + DT_NEEDED look reasonable for our musl-built
-- example. Aggregated by `LeanLoad.Test`.
-- ============================================================================
namespace LeanLoad.Parse.Test

open LeanLoad

/-- End-to-end smoke test: parse `bytes` and assert basics. -/
def run (bytes : ByteArray) : IO Nat := do
  let mut failures := 0

  match Parse.Parser.run bytes Parse.Header.parse with
  | .error e =>
      IO.eprintln s!"Header.parse failed: {e}"
      failures := failures + 1
  | .ok h =>
      if h.e_type != Spec.Header.ET_DYN then
        IO.eprintln s!"e_type: expected ET_DYN={Spec.Header.ET_DYN}, got {h.e_type}"
        failures := failures + 1
      if h.e_ehsize != 64 then
        IO.eprintln s!"e_ehsize: expected 64, got {h.e_ehsize}"
        failures := failures + 1
      if h.e_phentsize != 56 then
        IO.eprintln s!"e_phentsize: expected 56, got {h.e_phentsize}"
        failures := failures + 1
      match Parse.Parser.run bytes
              (Parse.Program.parseTable h.e_phoff.toNat h.e_phnum.toNat) with
      | .error e =>
          IO.eprintln s!"Program.parseTable failed: {e}"
          failures := failures + 1
      | .ok phs =>
          if phs.size != h.e_phnum.toNat then
            IO.eprintln s!"phnum mismatch: header says {h.e_phnum}, parsed {phs.size}"
            failures := failures + 1

  match Parse.File.parse bytes with
  | .error e =>
      IO.eprintln s!"File.parse failed: {e}"
      failures := failures + 1
  | .ok elf =>
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
  return failures

end LeanLoad.Parse.Test

/-
Aggregate ELF parser.

Walks an entire ELF file the way a loader needs to: header → program
headers → `.dynamic` → string table → dynamic symbol table →
relocation tables → `DT_NEEDED` strings → init/fini lists.

The dynamic symbol-table count is taken from `DT_HASH`'s `nchain`
field (gabi 08 § Hash Table). `DT_GNU_HASH`-only binaries are not yet
supported; musl always emits `DT_HASH`, so our test fixtures are
covered.
-/

import LeanLoad.Parse.Bytes
import LeanLoad.Parse.Header
import LeanLoad.Parse.Program
import LeanLoad.Parse.Dynamic
import LeanLoad.Parse.Symbol
import LeanLoad.Parse.Reloc

namespace LeanLoad.Parse.File

open LeanLoad.Parse

-- ============================================================================
-- Virtual-address ↔ file-offset translation
-- ============================================================================

/-- Translate a virtual address to a file offset by walking the
    `PT_LOAD` segments. Returns `none` if no `PT_LOAD` covers the
    address. -/
def vaToOffset (phdrs : Array Program.Header64) (va : UInt64) : Option Nat :=
  phdrs.findSome? fun ph =>
    if ph.p_type == Program.PT_LOAD
       && ph.p_vaddr ≤ va
       && va < ph.p_vaddr + ph.p_memsz then
      some ((va - ph.p_vaddr).toNat + ph.p_offset.toNat)
    else
      none

-- ============================================================================
-- Aggregated parse result
-- ============================================================================

/-- Everything the loader needs that comes from parsing a single ELF.
    Symbol table is omitted in v1 (see file header). -/
structure ParsedElf where
  bytes   : ByteArray
  header  : Header.ElfHeader64
  phdrs   : Array Program.Header64
  /-- The `.dynamic` array, empty if no `PT_DYNAMIC`. -/
  dyn     : Array Dynamic.Dyn64
  /-- The dynamic string table (`DT_STRTAB`), empty if absent. -/
  strtab  : Symbol.StringTable
  /-- Dynamic symbol table (`DT_SYMTAB`), sized via `DT_HASH`'s
      `nchain`. Empty if neither is present. -/
  symtab  : Array Symbol.Symbol64
  /-- Resolved `DT_NEEDED` strings, in dynamic-array order. -/
  needed  : Array String
  /-- `DT_SONAME` if present (the canonical name of this object). -/
  soname  : Option String
  /-- `DT_RUNPATH` (gabi 08; deprecated `DT_RPATH` falls back to this). -/
  runpath : Option String
  /-- General `Rela` relocations from `DT_RELA`. -/
  rela    : Array Reloc.Rela64
  /-- PLT relocations from `DT_JMPREL` (only `Rela` form supported). -/
  jmprel  : Array Reloc.Rela64
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

/-- Read the `d_un` (as `UInt64`) of the first matching tag. -/
private def dynVal? (dyn : Array Dynamic.Dyn64) (tag : UInt64) : Option UInt64 :=
  (Dynamic.find? dyn tag).map (·.d_un)

/-- For paired `(addr, size)` queries: returns both `d_un` values. -/
private def dynPair? (dyn : Array Dynamic.Dyn64) (tagA tagB : UInt64) : Option (UInt64 × UInt64) := do
  let a ← dynVal? dyn tagA
  let b ← dynVal? dyn tagB
  return (a, b)

/-- Translate a `.dynamic` virtual address to a file offset, with a
    descriptive error if the VA is not in any `PT_LOAD`. -/
private def vaOffsetOrThrow (phdrs : Array Program.Header64) (tag : String) (vaddr : UInt64)
    : Except String Nat :=
  match vaToOffset phdrs vaddr with
  | some off => .ok off
  | none     => .error s!"{tag} va 0x{vaddr.toNat} not in PT_LOAD"

/-- Run a parser at the file offset corresponding to a `(VA, ...)` entry
    in `.dynamic`. Returns `default` if the dynamic tag is absent. -/
private def parseAtDyn (phdrs : Array Program.Header64) (bytes : ByteArray)
    (tag : String) (vaddr? : Option UInt64) (default : α) (p : Nat → Parser α)
    : Except String α :=
  match vaddr? with
  | none       => .ok default
  | some vaddr => do
    let off ← vaOffsetOrThrow phdrs tag vaddr
    Parser.run bytes (p off)

-- ============================================================================
-- Top-level parser
-- ============================================================================

/-- Parse an entire ELF file into a `ParsedElf`. -/
def parse (bytes : ByteArray) : Except String ParsedElf := do
  let header ← Parser.run bytes Header.parse
  let phdrs  ← Parser.run bytes
                 (Program.parseTable header.e_phoff.toNat header.e_phnum.toNat)

  -- Dynamic array (if any).
  let dyn ← match phdrs.find? (·.p_type == Program.PT_DYNAMIC) with
            | none    => pure #[]
            | some ph => Parser.run bytes
                          (Dynamic.parseTable ph.p_offset.toNat ph.p_filesz.toNat)

  -- String table at DT_STRTAB, sized by DT_STRSZ.
  let strtab ← match dynPair? dyn Dynamic.DT_STRTAB Dynamic.DT_STRSZ with
    | none             => pure (ByteArray.mk #[])
    | some (vaddr, sz) =>
      parseAtDyn phdrs bytes "DT_STRTAB" (some vaddr) (ByteArray.mk #[])
        (fun off => Symbol.parseStringTable off sz.toNat)

  -- Symbol-table count from DT_HASH.nchain (4-byte word at offset 4
  -- of the hash table; layout: nbucket, nchain, ... per gabi 08).
  let symCount : Nat ←
    parseAtDyn phdrs bytes "DT_HASH" (dynVal? dyn Dynamic.DT_HASH) 0
      (fun off => do
        let nchain ← Bytes.atOffset (off + 4) Bytes.u32le
        return nchain.toNat)

  -- Dynamic symbol table.
  let symtab ←
    if symCount == 0 then pure #[]
    else parseAtDyn phdrs bytes "DT_SYMTAB" (dynVal? dyn Dynamic.DT_SYMTAB) #[]
           (fun off => Symbol.parseTable off symCount)

  -- DT_NEEDED entries (each is a strtab offset).
  let neededOffsets := (Dynamic.findAll dyn Dynamic.DT_NEEDED).map (·.d_un)
  let needed := neededOffsets.filterMap (fun off => Symbol.StringTable.lookup strtab off.toNat)

  let lookupStr (tag : UInt64) : Option String :=
    (dynVal? dyn tag).bind (fun off => Symbol.StringTable.lookup strtab off.toNat)
  let soname  := lookupStr Dynamic.DT_SONAME
  let runpath := lookupStr Dynamic.DT_RUNPATH <|> lookupStr Dynamic.DT_RPATH

  -- Rela tables. Both DT_RELA and DT_JMPREL use the same entry size.
  let parseRelaPair (tagAddr tagSz : UInt64) (label : String)
      : Except String (Array Reloc.Rela64) :=
    match dynPair? dyn tagAddr tagSz with
    | none             => .ok #[]
    | some (vaddr, sz) =>
      let count := sz.toNat / Reloc.Rela64.entrySize
      parseAtDyn phdrs bytes label (some vaddr) #[]
        (fun off => Reloc.parseRelaTable off count)
  let rela   ← parseRelaPair Dynamic.DT_RELA   Dynamic.DT_RELASZ   "DT_RELA"
  let jmprel ← parseRelaPair Dynamic.DT_JMPREL Dynamic.DT_PLTRELSZ "DT_JMPREL"

  -- Init / fini.
  let initFn := dynVal? dyn Dynamic.DT_INIT
  let finiFn := dynVal? dyn Dynamic.DT_FINI
  let parseFnArray (tagAddr tagSz : UInt64) (label : String)
      : Except String (Array UInt64) :=
    match dynPair? dyn tagAddr tagSz with
    | none           => .ok #[]
    | some (vaddr, sz) =>
      let count := sz.toNat / 8
      parseAtDyn phdrs bytes label (some vaddr) #[]
        (fun off => Bytes.parseArray off count Bytes.u64le)
  let initArr    ← parseFnArray Dynamic.DT_INIT_ARRAY    Dynamic.DT_INIT_ARRAYSZ    "DT_INIT_ARRAY"
  let finiArr    ← parseFnArray Dynamic.DT_FINI_ARRAY    Dynamic.DT_FINI_ARRAYSZ    "DT_FINI_ARRAY"
  let preinitArr ← parseFnArray Dynamic.DT_PREINIT_ARRAY Dynamic.DT_PREINIT_ARRAYSZ "DT_PREINIT_ARRAY"

  return {
    bytes, header, phdrs, dyn, strtab, symtab, needed, soname, runpath,
    rela, jmprel, initFn, finiFn, initArr, finiArr, preinitArr
  }

end LeanLoad.Parse.File

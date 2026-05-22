/-
Byte reads for checked ELF parsing.

This module owns the staging image assembled from file bytes. File offsets and
virtual addresses stay centralized here: content modules provide their parsers,
while `RawImage` translates dynamic-table virtual addresses through the early
checked `LoadMap` and applies those parsers to exact file slices.
-/

import LeanLoad.Parse.Reader
import LeanLoad.Parse.Ehdr.Basic
import LeanLoad.Parse.Strtab
import LeanLoad.Parse.Symbol.Raw
import LeanLoad.Parse.Symbol.SysVHash
import LeanLoad.Parse.Reloc.Raw
import LeanLoad.Parse.Phdr.Basic
import LeanLoad.Parse.Dyntab.Basic
import LeanLoad.Parse.Elf.LoadMap

namespace LeanLoad.Parse.Elf

open LeanLoad.Parse

/-- Direct file-offset data read before interpreting dynamic pointers. -/
structure RawHeaders where
  loadMap : LoadMap
  dyn     : Dyntab
  deriving Repr, Inhabited

/-- Dynamic content after following `.dynamic` virtual spans. -/
structure DynamicData where
  strtab  : Strtab
  symtab  : RawSymtab
  rela    : Array RawRela
  jmprel  : Array RawRela
  initArr : Array Vaddr
  finiArr : Array Vaddr
  deriving Repr, Inhabited

/-- Transient byte-decoded aggregate. `checkImage` immediately checks this into
    `LeanLoad.Parse.Elf`, so downstream code consumes the witnessed type. -/
structure RawImage where
  loadMap : LoadMap
  strtab  : Strtab
  symtab  : RawSymtab
  needed  : Array StrtabOff
  soname  : Option StrtabOff
  runpath : Option StrtabOff
  rela    : Array RawRela
  jmprel  : Array RawRela
  initArr : Array Vaddr
  finiArr : Array Vaddr
  deriving Repr, Inhabited

/-- Resolve a virtual span through the checked load map before reading at the
    translated file offset. -/
private def parseAtSpan [Monad m] (r : FileReader m) (loadMap : LoadMap)
    (span : VaddrSpan) (parser : Parser α) : ExceptT String m α :=
  match LoadMap.mapSpan loadMap span with
  | .ok mapped => parseAt r mapped.off span.size parser
  | .error e   => throw e

/-- Stage 1: read direct-file-offset data (`ehdr`, phdrs, `.dynamic`). -/
private def readHeaders [Monad m] (r : FileReader m) : ExceptT String m RawHeaders := do
  let header ← parseAt r 0 Ehdr.byteSize Ehdr.parse
  match LoadMap.checkHeader header with
  | .ok ()   => pure ()
  | .error e => throw e
  let phdrs ← parseAt r header.e_phoff
                 (Phdr.tableByteSize header.e_phnum.toNat)
                 (Phdr.parseTable header.e_phnum.toNat)
  let loadMap ←
    match LoadMap.ofHeaders r.fileSize header phdrs with
    | .ok map  => pure map
    | .error e => throw e
  let dyn ← match phdrs.find? (·.p_type == .dynamic) with
    | none    => pure #[]
    | some ph => parseAt r ph.p_offset ph.p_filesz
                   (Dyntab.parse ph.p_filesz)
  return { loadMap, dyn }

/-- Read `DT_HASH`'s SysV `nchain`, the dynamic-symbol count. -/
private def readSymCount [Monad m] (r : FileReader m) (loadMap : LoadMap)
    (hashVa : Option Vaddr) : ExceptT String m Nat := do
  match hashVa with
  | none    => pure 0
  | some va =>
      let span : VaddrSpan := { start := va, size := RawSysVHash.byteSize }
      let hdr ← parseAtSpan r loadMap span RawSysVHash.parse
      pure hdr.symCount

/-- Read `.dynstr` bytes. UTF-8 validation is delayed until `StrtabEntry`. -/
private def readStrtab [Monad m] (r : FileReader m) (loadMap : LoadMap)
    (loc : Option VaddrSpan) : ExceptT String m Strtab :=
  match loc with
  | none      => pure Strtab.empty
  | some span => parseAtSpan r loadMap span Strtab.parse

/-- Read `.dynsym`; count comes from `DT_HASH.nchain`. -/
private def readSymtab [Monad m] (r : FileReader m) (loadMap : LoadMap)
    (symVa : Option Vaddr) (count : Nat) : ExceptT String m RawSymtab := do
  if count == 0 then return #[]
  match symVa with
  | none    => pure #[]
  | some va =>
      let span : VaddrSpan := { start := va, size := RawSymtab.tableByteSize count }
      parseAtSpan r loadMap span (RawSymtab.parse count)

/-- Read a `DT_RELA` / `DT_JMPREL` table. -/
private def readRelas [Monad m] (label : String) (r : FileReader m)
    (loadMap : LoadMap) (loc : Option VaddrSpan) :
    ExceptT String m (Array RawRela) := do
  match loc with
  | none      => pure #[]
  | some span =>
      let count ←
        match RawRela.countFromByteSize span.size with
        | .ok count => pure count
        | .error e  => throw s!"parse: {label}: {e}"
      parseAtSpan r loadMap span (RawRela.parseTable count)

/-- Read a `DT_INIT_ARRAY` / `DT_FINI_ARRAY` table of 64-bit function
    pointers. -/
private def readVaddrArray [Monad m] (label : String) (r : FileReader m)
    (loadMap : LoadMap) (loc : Option VaddrSpan) :
    ExceptT String m (Array Vaddr) := do
  match loc with
  | none      => pure #[]
  | some span =>
      let bytes := span.size.toNat
      if bytes % 8 == 0 then
        parseAtSpan r loadMap span (decodeArray (α := Vaddr) (bytes / 8))
      else
        throw s!"parse: {label}: byte size {bytes} is not a multiple of 8"

/-- Stage 3: read all dynamic data pointed at by `.dynamic` accessors. -/
private def fetchDynamicData [Monad m] (r : FileReader m)
    (loadMap : LoadMap) (dyntab : Dyntab) : ExceptT String m DynamicData := do
  let strtabLoc ← liftExcept dyntab.strtab?
  let symtabHash ← liftExcept dyntab.symtabHash?
  let symCount ← readSymCount r loadMap (symtabHash.map (·.2))
  let strtab   ← readStrtab   r loadMap strtabLoc
  let symtab   ← readSymtab   r loadMap (symtabHash.map (·.1)) symCount
  let rela     ← readRelas "DT_RELA" r loadMap (← liftExcept dyntab.rela?)
  let jmprel   ← readRelas "DT_JMPREL" r loadMap (← liftExcept dyntab.jmprel?)
  let initArr  ← readVaddrArray "DT_INIT_ARRAY" r loadMap (← liftExcept dyntab.initArr?)
  let finiArr  ← readVaddrArray "DT_FINI_ARRAY" r loadMap (← liftExcept dyntab.finiArr?)
  return { strtab, symtab, rela, jmprel, initArr, finiArr }

/-- Byte-decode an ELF into the transient staging image. -/
def readImageM [Monad m] (r : FileReader m) : ExceptT String m RawImage := do
  let h ← readHeaders r
  let c ← fetchDynamicData r h.loadMap h.dyn
  let soname ← liftExcept h.dyn.soname?
  let runpath ← liftExcept h.dyn.runpath?
  return {
    loadMap := h.loadMap,
    strtab  := c.strtab,
    symtab  := c.symtab,
    needed  := h.dyn.needed,
    soname,
    runpath,
    rela    := c.rela,
    jmprel  := c.jmprel,
    initArr := c.initArr,
    finiArr := c.finiArr
  }

end LeanLoad.Parse.Elf

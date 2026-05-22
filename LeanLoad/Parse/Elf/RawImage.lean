/-
Byte reads for checked ELF parsing.

This module owns the staging image assembled from file bytes. File offsets and
virtual addresses stay centralized here: content modules provide their parsers,
while `RawImage` translates dynamic-table virtual addresses through the early
checked `LoadMap` and applies those parsers to exact file slices.
-/

import LeanLoad.Parse.Reader
import LeanLoad.Parse.Ehdr.Raw
import LeanLoad.Parse.Strtab
import LeanLoad.Parse.Symbol.Raw
import LeanLoad.Parse.Symbol.SysVHash
import LeanLoad.Parse.Reloc.Raw
import LeanLoad.Parse.Phdr.Raw
import LeanLoad.Parse.Dyntab.Raw
import LeanLoad.Parse.Dyntab.Info
import LeanLoad.Parse.Elf.LoadMap

namespace LeanLoad.Parse.Elf

open LeanLoad.Parse

/-- Direct file-offset data read before interpreting dynamic pointers. -/
structure RawHeaders where
  loadMap : LoadMap
  dyn     : RawDyntab
  deriving Repr, Inhabited

/-- Dynamic content after following `DynInfo` pointers. -/
structure DynamicData where
  strtab  : RawStrtab
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
  strtab  : RawStrtab
  symtab  : RawSymtab
  needed  : Array StrtabOff
  soname  : Option StrtabOff
  runpath : Option StrtabOff
  rela    : Array RawRela
  jmprel  : Array RawRela
  initArr : Array Vaddr
  finiArr : Array Vaddr
  deriving Repr, Inhabited

/-- Resolve `va` through the checked load map before reading at the translated
    file offset. -/
private def parseAtVa [Monad m] (r : FileReader m) (loadMap : LoadMap)
    (va : Vaddr) (len : ByteSize) (parser : Parser α) : ExceptT String m α :=
  match LoadMap.mapVaddr loadMap va len with
  | .ok mapped => parseAt r mapped.off len parser
  | .error e   => throw e

/-- Stage 1: read direct-file-offset data (`ehdr`, phdrs, `.dynamic`). -/
private def readHeaders [Monad m] (r : FileReader m) : ExceptT String m RawHeaders := do
  let header ← parseAt r 0 Ehdr.byteSize Ehdr.parse
  match LoadMap.checkHeader header with
  | .ok ()   => pure ()
  | .error e => throw e
  let phdrs ← parseAt r header.e_phoff
                 (RawPhdr.tableByteSize header.e_phnum.toNat)
                 (RawPhdr.parseTable header.e_phnum.toNat)
  let loadMap ←
    match LoadMap.ofHeaders r.fileSize header phdrs with
    | .ok map  => pure map
    | .error e => throw e
  let dyn ← match phdrs.find? (·.p_type == .dynamic) with
    | none    => pure #[]
    | some ph => parseAt r ph.p_offset ph.p_filesz
                   (RawDyntab.parse ph.p_filesz)
  return { loadMap, dyn }

/-- Read `DT_HASH`'s SysV `nchain`, the dynamic-symbol count. -/
private def readSymCount [Monad m] (r : FileReader m) (loadMap : LoadMap)
    (hashVa : Option Vaddr) : ExceptT String m Nat := do
  match hashVa with
  | none    => pure 0
  | some va =>
      let hdr ← parseAtVa r loadMap va RawSysVHash.byteSize RawSysVHash.parse
      pure hdr.symCount

/-- Read `.dynstr` bytes. UTF-8 validation is delayed until `StrtabEntry`. -/
private def readStrtab [Monad m] (r : FileReader m) (loadMap : LoadMap)
    (loc : Option (Vaddr × ByteSize)) : ExceptT String m RawStrtab :=
  match loc with
  | none       => pure RawStrtab.empty
  | some (v,s) => parseAtVa r loadMap v s RawStrtab.parse

/-- Read `.dynsym`; count comes from `DT_HASH.nchain`. -/
private def readSymtab [Monad m] (r : FileReader m) (loadMap : LoadMap)
    (symVa : Option Vaddr) (count : Nat) : ExceptT String m RawSymtab := do
  if count == 0 then return #[]
  match symVa with
  | none    => pure #[]
  | some va => parseAtVa r loadMap va (RawSymtab.tableByteSize count)
                 (RawSymtab.parse count)

/-- Read a `DT_RELA` / `DT_JMPREL` table. -/
private def readRelas [Monad m] (label : String) (r : FileReader m)
    (loadMap : LoadMap) (loc : Option (Vaddr × ByteSize)) :
    ExceptT String m (Array RawRela) := do
  match loc with
  | none       => pure #[]
  | some (v,s) =>
      let count ←
        match RawRela.countFromByteSize s with
        | .ok count => pure count
        | .error e  => throw s!"parse: {label}: {e}"
      parseAtVa r loadMap v s (RawRela.parseTable count)

/-- Read a `DT_INIT_ARRAY` / `DT_FINI_ARRAY` table of 64-bit function
    pointers. -/
private def readVaddrArray [Monad m] (label : String) (r : FileReader m)
    (loadMap : LoadMap) (loc : Option (Vaddr × ByteSize)) :
    ExceptT String m (Array Vaddr) := do
  match loc with
  | none       => pure #[]
  | some (v,s) =>
      let bytes := s.toNat
      if bytes % 8 == 0 then
        parseAtVa r loadMap v s (decodeArray (α := Vaddr) (bytes / 8))
      else
        throw s!"parse: {label}: byte size {bytes} is not a multiple of 8"

/-- Stage 3: read all dynamic data pointed at by `DynInfo`. -/
private def fetchDynamicData [Monad m] (r : FileReader m)
    (loadMap : LoadMap) (info : DynInfo) : ExceptT String m DynamicData := do
  let symCount ← readSymCount r loadMap info.hash
  let strtab   ← readStrtab   r loadMap info.strtab
  let symtab   ← readSymtab   r loadMap info.symtab symCount
  let rela     ← readRelas "DT_RELA" r loadMap info.rela
  let jmprel   ← readRelas "DT_JMPREL" r loadMap info.jmprel
  let initArr  ← readVaddrArray "DT_INIT_ARRAY" r loadMap info.initArr
  let finiArr  ← readVaddrArray "DT_FINI_ARRAY" r loadMap info.finiArr
  return { strtab, symtab, rela, jmprel, initArr, finiArr }

/-- Byte-decode an ELF into the transient staging image. -/
def readImageM [Monad m] (r : FileReader m) : ExceptT String m RawImage := do
  let h ← readHeaders r
  let info ←
    match DynInfo.ofTable h.dyn with
    | .ok info => pure info
    | .error e => throw e
  let c ← fetchDynamicData r h.loadMap info
  return {
    loadMap := h.loadMap,
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

end LeanLoad.Parse.Elf

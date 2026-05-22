/-
Raw ELF staging image.

This module owns the byte-decoded `Dynamic` stage. File offsets and ELF
addresses stay centralized here: content modules provide their parsers, while
`Dynamic.ImageView` translates dynamic-table ELF-address ranges to exact file
slices.
-/

import LeanLoad.Parse.Reader
import LeanLoad.Parse.ImageView.ElfHeader.Basic
import LeanLoad.Parse.Dynamic.Strtab
import LeanLoad.Parse.Dynamic.Symbol.Raw
import LeanLoad.Parse.Dynamic.Symbol.SysVHash
import LeanLoad.Parse.Dynamic.Reloc.Raw
import LeanLoad.Parse.ImageView.ProgramHeader.Basic
import LeanLoad.Parse.Dynamic.Dyntab.Basic
import LeanLoad.Parse.ImageView.Basic

namespace LeanLoad.Parse

/-- Transient byte-decoded ELF. `Elf.checkImage` immediately checks this into
    `LeanLoad.Parse.Elf`, so downstream code consumes the witnessed type. -/
structure Dynamic where
  header  : ElfHeader
  segments : Segments
  strtab  : Strtab
  symtab  : RawSymtab
  needed  : Array StrtabOff
  soname  : Option StrtabOff
  runpath : Option StrtabOff
  rela    : Array RawRela
  jmprel  : Array RawRela
  initArr : Array Eaddr
  finiArr : Array Eaddr
  deriving Repr

namespace Dynamic

/-- Dynamic content after following `.dynamic` ELF-address ranges. -/
private structure DynamicData where
  strtab  : Strtab
  symtab  : RawSymtab
  rela    : Array RawRela
  jmprel  : Array RawRela
  initArr : Array Eaddr
  finiArr : Array Eaddr
  deriving Repr, Inhabited

/-- Resolve an ELF-address range through the checked load map before reading at the
    translated file offset. -/
private def parseAtRange [Monad m] (r : FileReader m) (view : ImageView)
    (range : EaddrRange) (parser : Parser α) : ExceptT String m α :=
  match ImageView.mapRange view r.fileSize range with
  | .ok mapped => parseAtFileRange r mapped.fileRange parser
  | .error e   => throw e

/-- Read `DT_HASH`'s SysV `nchain`, the dynamic-symbol count. -/
private def readSymCount [Monad m] (r : FileReader m) (view : ImageView)
    (hashVa : Option Eaddr) : ExceptT String m Nat := do
  match hashVa with
  | none    => pure 0
  | some va =>
      let range : EaddrRange := { start := va, size := RawSysVHash.byteSize }
      let hdr ← parseAtRange r view range RawSysVHash.parse
      pure hdr.symCount

/-- Read `.dynstr` bytes. UTF-8 validation is delayed until `StrtabEntry`. -/
private def readStrtab [Monad m] (r : FileReader m) (view : ImageView)
    (loc : Option EaddrRange) : ExceptT String m Strtab :=
  match loc with
  | none       => pure Strtab.empty
  | some range => parseAtRange r view range Strtab.parse

/-- Read `.dynsym`; count comes from `DT_HASH.nchain`. -/
private def readSymtab [Monad m] (r : FileReader m) (view : ImageView)
    (symVa : Option Eaddr) (count : Nat) : ExceptT String m RawSymtab := do
  if count == 0 then return #[]
  match symVa with
  | none    => pure #[]
  | some va =>
      let range : EaddrRange := { start := va, size := RawSymtab.tableByteSize count }
      parseAtRange r view range (RawSymtab.parse count)

/-- Read `.dynsym` and its SysV hash header. LeanLoad requires `DT_SYMTAB` and
    `DT_HASH` to appear together because `DT_HASH.nchain` supplies the symbol
    count. -/
private def readSymtabData [Monad m] (r : FileReader m) (view : ImageView)
    (symVa hashVa : Option Eaddr) : ExceptT String m RawSymtab := do
  match symVa, hashVa with
  | none, none => pure #[]
  | some _, none => throw "parse: DT_SYMTAB present without DT_HASH"
  | none, some _ => throw "parse: DT_HASH present without DT_SYMTAB"
  | some _, some _ =>
      let symCount ← readSymCount r view hashVa
      readSymtab r view symVa symCount

/-- Read a `DT_RELA` / `DT_JMPREL` table. -/
private def readRelas [Monad m] (label : String) (r : FileReader m)
    (view : ImageView) (loc : Option EaddrRange) :
    ExceptT String m (Array RawRela) := do
  match loc with
  | none       => pure #[]
  | some range =>
      let count ←
        match RawRela.countFromByteSize range.size with
        | .ok count => pure count
        | .error e  => throw s!"parse: {label}: {e}"
      parseAtRange r view range (RawRela.parseTable count)

/-- Read `DT_JMPREL` after validating its separate `DT_PLTREL` encoding tag. -/
private def readJmprel [Monad m] (r : FileReader m) (view : ImageView)
    (loc : Option EaddrRange) (kind : Option PltRelKind) :
    ExceptT String m (Array RawRela) := do
  match loc, kind with
  | none, _ => pure #[]
  | some _, none => throw "parse: DT_JMPREL present without DT_PLTREL"
  | some _, some .rel => throw "parse: DT_PLTREL=DT_REL, expected DT_RELA"
  | some range, some .rela => readRelas "DT_JMPREL" r view (some range)

/-- Read a `DT_INIT_ARRAY` / `DT_FINI_ARRAY` table of 64-bit function
    pointers. -/
private def readEaddrArray [Monad m] (label : String) (r : FileReader m)
    (view : ImageView) (loc : Option EaddrRange) :
    ExceptT String m (Array Eaddr) := do
  match loc with
  | none      => pure #[]
  | some range =>
      let bytes := range.size.toNat
      if bytes % 8 == 0 then
        parseAtRange r view range (decodeArray (α := Eaddr) (bytes / 8))
      else
        throw s!"parse: {label}: byte size {bytes} is not a multiple of 8"

/-- Stage 3: read all dynamic data pointed at by `.dynamic` accessors. -/
private def fetchDynamicData [Monad m] (r : FileReader m)
    (view : ImageView) (dyntab : Dyntab) : ExceptT String m DynamicData := do
  let strtabLoc ← liftExcept dyntab.strtab?
  let symtabVa ← liftExcept dyntab.symtab?
  let hashVa ← liftExcept dyntab.hash?
  let strtab   ← readStrtab   r view strtabLoc
  let symtab   ← readSymtabData r view symtabVa hashVa
  let rela     ← readRelas "DT_RELA" r view (← liftExcept dyntab.rela?)
  let jmprel   ← readJmprel r view (← liftExcept dyntab.jmprel?) (← liftExcept dyntab.pltrel?)
  let initArr  ← readEaddrArray "DT_INIT_ARRAY" r view (← liftExcept dyntab.initArr?)
  let finiArr  ← readEaddrArray "DT_FINI_ARRAY" r view (← liftExcept dyntab.finiArr?)
  return { strtab, symtab, rela, jmprel, initArr, finiArr }

/-- Byte-decode an ELF into the transient raw staging image. -/
def readM [Monad m] (r : FileReader m) : ExceptT String m Dynamic := do
  let header ← parseAt r 0 ElfHeader.byteSize ElfHeader.parse
  let phdrs ← parseAt r header.e_phoff
                 (ProgramHeader.tableByteSize header.e_phnum.toNat)
                 (ProgramHeader.parseTable header.e_phnum.toNat)
  let view ←
    match ImageView.ofHeaders r.fileSize header phdrs with
    | .ok view => pure view
    | .error e => throw e
  let dyn ← match phdrs.find? (·.p_type == .dynamic) with
    | none    => pure #[]
    | some ph => parseAt r ph.p_offset ph.p_filesz
                   (Dyntab.parse ph.p_filesz)
  let c ← fetchDynamicData r view dyn
  let soname ← liftExcept (Dyntab.soname? dyn)
  let runpath ← liftExcept (Dyntab.runpath? dyn)
  return {
    header := view.header,
    segments := view.segments,
    strtab  := c.strtab,
    symtab  := c.symtab,
    needed  := Dyntab.needed dyn,
    soname,
    runpath,
    rela    := c.rela,
    jmprel  := c.jmprel,
    initArr := c.initArr,
    finiArr := c.finiArr }

end Dynamic

end LeanLoad.Parse

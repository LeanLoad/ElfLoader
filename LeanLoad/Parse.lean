/-
Checked ELF parse-stage product and public parse entry points.
-/

import LeanLoad.Parse.Dynamic.Dyntab.Basic
import LeanLoad.Parse.Dynamic.InitFini
import LeanLoad.Parse.Dynamic.Reloc.Table
import LeanLoad.Parse.Dynamic.Symbol.Checked
import LeanLoad.Parse.Dynamic.Symbol.SysVHash
import LeanLoad.Parse.LoadMap.Basic
import LeanLoad.Parse.LoadMap.ProgramHeader.Basic
import LeanLoad.Parse.Reader
import LeanLoad.Runtime

namespace LeanLoad.Parse

open Dynamic

/-- The checked form of an ELF.

    Construction enforces per-rela segment containment, checked symbol names, and
    init/fini target coverage. Header policy, PT_LOAD well-formedness, and
    dynamic string resolution are established by the parse driver below. -/
structure Elf where
  /-- Parsed ELF header. `ElfHeader` is already semantically typed: magic,
      identifiers, `e_type`, `e_machine`, addresses, and sentinels are decoded
      to parse-layer field types. -/
  header   : ElfHeader
  symtab   : Array Symbol
  needed   : Array String
  soname   : Option String
  runpath  : Option String
  /-- Checked PT_LOAD array, in phdr order, with array-level
      ordering/disjointness witnessed. -/
  segments : SegmentTable
  /-- Dynamic relocations located in their target segments. -/
  relocs   : Reloc.RelocTable segments
  /-- `DT_INIT_ARRAY` entries — ctors, walked forward on startup. Each entry is
      zero or targets an executable PT_LOAD in `segments`. -/
  initArr  : InitFiniArray segments
  /-- `DT_FINI_ARRAY` entries — dtors, walked backward on exit. Each entry is
      zero or targets an executable PT_LOAD in `segments`. -/
  finiArr  : InitFiniArray segments
  deriving Repr

/-- Decode bytes from an already-checked file range.

    This is the parse orchestration seam: `Reader` supplies exact bytes for a
    witnessed range, and `Decoder` interprets those bytes as a typed value. -/
private def decodeRange [Monad m] (r : FileReader m)
    {off : FileOff} {len : ByteSize} (range : FileRange r.fileSize off len)
    (decoder : Decoder α) : ExceptT String m α := do
  let bytes ← readRange r range
  match Decoder.run bytes decoder with
  | .ok v    => pure v
  | .error e => throw e

/-- Resolve a dynamic string-table offset while preserving diagnostic context
    for the tag that supplied it. -/
private def resolveStrtabOff (label : String) (strtab : Strtab) (off : StrtabOff) :
    Except String String :=
  match StrtabEntry.ofOff strtab off with
  | .ok entry => .ok entry.value
  | .error e  => .error s!"parse: {label}: {e}"

/-- Resolve an optional dynamic string-table reference with the tag name in
    diagnostics. -/
private def resolveStrtabOff? (label : String) (strtab : Strtab) :
    Option StrtabOff → Except String (Option String)
  | none     => .ok none
  | some off => do
      let s ← resolveStrtabOff label strtab off
      pure (some s)

/-- Read `DT_HASH`'s SysV `nchain`, the dynamic-symbol count. -/
private def readSymCount [Monad m] (r : FileReader m) (view : LoadMap)
    (hashVa : Option Eaddr) : ExceptT String m Nat := do
  match hashVa with
  | none    => pure 0
  | some va =>
      let range : EaddrRange := { start := va, size := RawSysVHash.byteSize }
      let mapped ← liftExcept (LoadMap.mapRange view r.fileSize range)
      let hdr : RawSysVHash ← decodeRange r mapped.fileRange Decodable.decoder
      pure hdr.symCount

/-- Read `.dynstr` bytes. UTF-8 validation is delayed until `StrtabEntry`. -/
private def readStrtab [Monad m] (r : FileReader m) (view : LoadMap)
    (loc : Option EaddrRange) : ExceptT String m Strtab :=
  match loc with
  | none       => pure Strtab.empty
  | some range => do
      let mapped ← liftExcept (LoadMap.mapRange view r.fileSize range)
      decodeRange r mapped.fileRange Strtab.decode

/-- Read `.dynsym`; count comes from `DT_HASH.nchain`. -/
private def readSymtab [Monad m] (r : FileReader m) (view : LoadMap)
    (symVa : Option Eaddr) (count : Nat) : ExceptT String m RawSymtab := do
  if count == 0 then return #[]
  match symVa with
  | none    => pure #[]
  | some va =>
      let range : EaddrRange := { start := va, size := RawSymtab.tableByteSize count }
      let mapped ← liftExcept (LoadMap.mapRange view r.fileSize range)
      decodeRange r mapped.fileRange (RawSymtab.decode count)

/-- Read `.dynsym` and its SysV hash header. LeanLoad requires `DT_SYMTAB` and
    `DT_HASH` to appear together because `DT_HASH.nchain` supplies the symbol
    count. -/
private def readSymtabData [Monad m] (r : FileReader m) (view : LoadMap)
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
    (view : LoadMap) (loc : Option EaddrRange) :
    ExceptT String m (Array RawRela) := do
  match loc with
  | none       => pure #[]
  | some range =>
      let count ←
        match RawRela.countFromByteSize range.size with
        | .ok count => pure count
        | .error e  => throw s!"parse: {label}: {e}"
      let mapped ← liftExcept (LoadMap.mapRange view r.fileSize range)
      decodeRange r mapped.fileRange (RawRela.decodeTable count)

/-- Read `DT_JMPREL` after validating its separate `DT_PLTREL` encoding tag. -/
private def readJmprel [Monad m] (r : FileReader m) (view : LoadMap)
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
    (view : LoadMap) (loc : Option EaddrRange) :
    ExceptT String m (Array Eaddr) := do
  match loc with
  | none      => pure #[]
  | some range =>
      let bytes := range.size.toNat
      if bytes % 8 == 0 then
        let mapped ← liftExcept (LoadMap.mapRange view r.fileSize range)
        decodeRange r mapped.fileRange (Decoder.array (bytes / 8) (Decodable.decoder (α := Eaddr)))
      else
        throw s!"parse: {label}: byte size {bytes} is not a multiple of 8"

/-- Monad-polymorphic checked parse. The `FileReader m` abstracts byte delivery;
    all parse and validation errors flow through `ExceptT`. -/
def parseM [Monad m] (r : FileReader m) : ExceptT String m Elf := do
  let headerLen := ByteSize.ofNat ElfHeaderSize
  let headerRange ← liftExcept (checkRange r (0 : FileOff) headerLen)
  let header : ElfHeader ← decodeRange r headerRange Decodable.decoder
  let phdrLen := ProgramHeader.tableByteSize header.e_phnum.toNat
  let phdrRange ← liftExcept (checkRange r header.e_phoff phdrLen)
  let programHeaders ← decodeRange r phdrRange (ProgramHeader.decodeTable header.e_phnum.toNat)
  let view ←
    match LoadMap.ofHeaders r.fileSize header programHeaders with
    | .ok view => pure view
    | .error e => throw e
  let dyn ← match programHeaders.find? (·.p_type == .dynamic) with
    | none    => pure #[]
    | some ph =>
        let dynRange ← liftExcept (checkRange r ph.p_offset ph.p_filesz)
        decodeRange r dynRange (Dyntab.decode ph.p_filesz)
  let strtab ← readStrtab r view (← liftExcept (Dyntab.strtab? dyn))
  let symtabRaw ←
    readSymtabData r view (← liftExcept (Dyntab.symtab? dyn)) (← liftExcept (Dyntab.hash? dyn))
  let rela ← readRelas "DT_RELA" r view (← liftExcept (Dyntab.rela? dyn))
  let jmprel ←
    readJmprel r view (← liftExcept (Dyntab.jmprel? dyn)) (← liftExcept (Dyntab.pltrel? dyn))
  let initArrRaw ← readEaddrArray "DT_INIT_ARRAY" r view (← liftExcept (Dyntab.initArr? dyn))
  let finiArrRaw ← readEaddrArray "DT_FINI_ARRAY" r view (← liftExcept (Dyntab.finiArr? dyn))
  let needed ← liftExcept ((Dyntab.needed dyn).mapM (resolveStrtabOff "DT_NEEDED" strtab))
  let soname ← liftExcept (resolveStrtabOff? "DT_SONAME" strtab (← Dyntab.soname? dyn))
  let runpath ← liftExcept (resolveStrtabOff? "DT_RUNPATH" strtab (← Dyntab.runpath? dyn))
  let relocs ← liftExcept (Reloc.locateAll view.segments rela jmprel)
  let symtab ← liftExcept (symtabRaw.mapM (Symbol.ofRaw strtab))
  let initArr ← liftExcept (InitFiniArray.ofRaw "DT_INIT_ARRAY" view.segments initArrRaw)
  let finiArr ← liftExcept (InitFiniArray.ofRaw "DT_FINI_ARRAY" view.segments finiArrRaw)
  return {
    header := view.header,
    segments := view.segments,
    symtab,
    needed,
    soname,
    runpath,
    relocs,
    initArr,
    finiArr }

/-- Production entry point: parse and check an open file. -/
def parse (f : Runtime.File) : IO Elf := do
  match ← (parseM (Runtime.fileReader f)).run with
  | .ok elf  => pure elf
  | .error e => throw (IO.userError e)

end LeanLoad.Parse

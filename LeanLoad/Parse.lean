/-
Checked ELF parse-stage product and monad-polymorphic driver.
-/

import LeanLoad.Parse.Dynamic.Dyntab.Basic
import LeanLoad.Parse.Dynamic.Reloc.Table
import LeanLoad.Parse.Dynamic.Symbol.Checked
import LeanLoad.Parse.Dynamic.Symbol.SysVHash
import LeanLoad.Parse.CallTargets
import LeanLoad.Parse.LoadMap.Basic
import LeanLoad.Parse.LoadMap.ProgramHeader.Basic
import LeanLoad.Runtime.FileOps

namespace LeanLoad.Parse

open Dynamic

private def readBytes [Monad m] (ops : Runtime.FileOps m h) (file : h)
    (off : FileOff) (len : ByteSize) : ExceptT String m ByteArray := do
  let fileSize := ops.fileSize file
  if off.toNat + len.toNat ≤ fileSize.toNat then
    let bytes ← ops.pread file off.val len.val
    if bytes.size == len.toNat then
      pure bytes
    else
      throw s!"read at file offset 0x{off.toNat} requested {len.toNat} bytes, \
        got {bytes.size}"
  else
    throw s!"read at file offset 0x{off.toNat} requested {len.toNat} bytes, \
      past file size {fileSize.toNat}"

private def parseBytesAt [Monad m] (ops : Runtime.FileOps m h) (file : h)
    (off : FileOff) (len : ByteSize) (decoder : Decoder α) : ExceptT String m α := do
  let bytes ← readBytes ops file off len
  liftExcept (Decoder.run bytes decoder)

private def parseAt [Monad m] [Decodable α] (ops : Runtime.FileOps m h)
    (file : h) (off : FileOff) : ExceptT String m α :=
  parseBytesAt ops file off (ByteSize.ofNat (Decodable.byteSize (α := α)))
    (Decodable.decoder (α := α))

private def parseArrayAt [Monad m] [Decodable α] (ops : Runtime.FileOps m h)
    (file : h) (off : FileOff) (count : Nat) : ExceptT String m (Array α) :=
  parseBytesAt ops file off (ByteSize.ofEntries count (Decodable.byteSize (α := α)))
    (Decoder.array count (Decodable.decoder (α := α)))

/-- The checked form of an ELF.

    Construction enforces per-rela segment containment, checked symbol names, and
    callable target coverage. Header policy, PT_LOAD well-formedness, and
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
  /-- Checked `e_entry`, `DT_INIT_ARRAY`, and `DT_FINI_ARRAY` call targets.
      Each slot is zero or targets an executable PT_LOAD in `segments`. -/
  callTargets : CallTargets segments
  deriving Repr

private def parseMapped [Monad m] (ops : Runtime.FileOps m h) (file : h)
    (view : LoadMap) (range : EaddrRange) (decoder : Decoder α) :
    ExceptT String m α := do
  let mapped ← liftExcept (LoadMap.mapRange view range)
  parseBytesAt ops file mapped.fileOff range.size decoder

/-- Read `.dynstr` bytes. UTF-8 validation is delayed until `StrtabEntry`. -/
private def readMappedStrtab [Monad m] (ops : Runtime.FileOps m h) (file : h)
    (view : LoadMap) (loc : Option EaddrRange) : ExceptT String m Strtab :=
  match loc with
  | none       => pure Strtab.empty
  | some range => parseMapped ops file view range Strtab.decode

/-- Read `.dynsym` using `DT_HASH.nchain` as the symbol count. LeanLoad requires
    `DT_SYMTAB` and `DT_HASH` to appear together. -/
private def readMappedSymtab [Monad m] (ops : Runtime.FileOps m h) (file : h)
    (view : LoadMap) (symVa hashVa : Option Eaddr) : ExceptT String m RawSymtab := do
  match symVa, hashVa with
  | none, none => pure #[]
  | some _, none => throw "parse: DT_SYMTAB present without DT_HASH"
  | none, some _ => throw "parse: DT_HASH present without DT_SYMTAB"
  | some symVa, some hashVa =>
      let hashRange : EaddrRange := { start := hashVa, size := RawSysVHash.byteSize }
      let hash : RawSysVHash ← parseMapped ops file view hashRange Decodable.decoder
      if hash.symCount == 0 then
        return #[]
      let symRange : EaddrRange := { start := symVa, size := RawSymtab.tableByteSize hash.symCount }
      parseMapped ops file view symRange (RawSymtab.decode hash.symCount)

/-- Read a `DT_RELA` / `DT_JMPREL` table. -/
private def readMappedRelaTable [Monad m] (ops : Runtime.FileOps m h) (file : h)
    (view : LoadMap) (label : String) (loc : Option EaddrRange) :
    ExceptT String m (Array RawRela) := do
  match loc with
  | none       => pure #[]
  | some range =>
      let count ←
        match RawRela.countFromByteSize range.size with
        | .ok count => pure count
        | .error e  => throw s!"parse: {label}: {e}"
      parseMapped ops file view range (RawRela.decodeTable count)

/-- Read `DT_JMPREL` after validating its separate `DT_PLTREL` encoding tag. -/
private def readMappedJmprel [Monad m] (ops : Runtime.FileOps m h) (file : h)
    (view : LoadMap) (loc : Option EaddrRange) (kind : Option PltRelKind) :
    ExceptT String m (Array RawRela) := do
  match loc, kind with
  | none, _ => pure #[]
  | some _, none => throw "parse: DT_JMPREL present without DT_PLTREL"
  | some _, some .rel => throw "parse: DT_PLTREL=DT_REL, expected DT_RELA"
  | some range, some .rela => readMappedRelaTable ops file view "DT_JMPREL" (some range)

/-- Read a `DT_INIT_ARRAY` / `DT_FINI_ARRAY` table of 64-bit function
    pointers. -/
private def readMappedEaddrArray [Monad m] (ops : Runtime.FileOps m h) (file : h)
    (view : LoadMap) (label : String) (loc : Option EaddrRange) :
    ExceptT String m (Array Eaddr) := do
  match loc with
  | none      => pure #[]
  | some range =>
      let bytes := range.size.toNat
      let entrySize := Decodable.byteSize (α := Eaddr)
      if bytes % entrySize == 0 then
        parseMapped ops file view range
          (Decoder.array (bytes / entrySize) (Decodable.decoder (α := Eaddr)))
      else
        throw s!"parse: {label}: byte size {bytes} is not a multiple of {entrySize}"

namespace Dyntab

/-- Read `.dynstr` through the checked load map using this dynamic table's tags. -/
private def readStrtab [Monad m] (dyn : Dyntab) (ops : Runtime.FileOps m h)
    (file : h) (view : LoadMap) :
    ExceptT String m Strtab := do
  readMappedStrtab ops file view (← liftExcept dyn.strtab?)

/-- Read `.dynsym` through the checked load map using this dynamic table's tags. -/
private def readSymtab [Monad m] (dyn : Dyntab) (ops : Runtime.FileOps m h)
    (file : h) (view : LoadMap) :
    ExceptT String m RawSymtab := do
  readMappedSymtab ops file view (← liftExcept dyn.symtab?) (← liftExcept dyn.hash?)

/-- Read `DT_RELA` relocations through the checked load map. -/
private def readRelaTable [Monad m] (dyn : Dyntab) (ops : Runtime.FileOps m h)
    (file : h) (view : LoadMap) :
    ExceptT String m (Array RawRela) := do
  readMappedRelaTable ops file view "DT_RELA" (← liftExcept dyn.rela?)

/-- Read `DT_JMPREL` relocations through the checked load map. -/
private def readJmprelTable [Monad m] (dyn : Dyntab) (ops : Runtime.FileOps m h)
    (file : h) (view : LoadMap) :
    ExceptT String m (Array RawRela) := do
  readMappedJmprel ops file view (← liftExcept dyn.jmprel?) (← liftExcept dyn.pltrel?)

/-- Read `DT_INIT_ARRAY` function pointers through the checked load map. -/
private def readInitArray [Monad m] (dyn : Dyntab) (ops : Runtime.FileOps m h)
    (file : h) (view : LoadMap) :
    ExceptT String m (Array Eaddr) := do
  readMappedEaddrArray ops file view "DT_INIT_ARRAY" (← liftExcept dyn.initArr?)

/-- Read `DT_FINI_ARRAY` function pointers through the checked load map. -/
private def readFiniArray [Monad m] (dyn : Dyntab) (ops : Runtime.FileOps m h)
    (file : h) (view : LoadMap) :
    ExceptT String m (Array Eaddr) := do
  readMappedEaddrArray ops file view "DT_FINI_ARRAY" (← liftExcept dyn.finiArr?)

end Dyntab

/-- Monad-polymorphic checked parse over the runtime file capability. -/
def parseM [Monad m] (ops : Runtime.FileOps m h) (file : h) : ExceptT String m Elf := do
  let header : ElfHeader ← parseAt ops file 0
  let programHeaders ←
    parseArrayAt (α := ProgramHeader) ops file header.e_phoff header.e_phnum.toNat
  let view ←
    match LoadMap.ofHeaders (ops.fileSize file) header programHeaders with
    | .ok view => pure view
    | .error e => throw e
  let dyn : Dyntab ← match programHeaders.find? (·.p_type == .dynamic) with
    | none    => pure #[]
    | some ph =>
        parseBytesAt ops file ph.p_offset ph.p_filesz (Dyntab.decode ph.p_filesz)
  let strtab : Strtab ← Dyntab.readStrtab dyn ops file view
  let symtabRaw ← Dyntab.readSymtab dyn ops file view
  let rela ← Dyntab.readRelaTable dyn ops file view
  let jmprel ← Dyntab.readJmprelTable dyn ops file view
  let initArrRaw ← Dyntab.readInitArray dyn ops file view
  let finiArrRaw ← Dyntab.readFiniArray dyn ops file view
  let needed ← liftExcept ((Dyntab.needed dyn).mapM (strtab.resolve "DT_NEEDED"))
  let soname ← liftExcept (strtab.resolve? "DT_SONAME" (← Dyntab.soname? dyn))
  let runpath ← liftExcept (strtab.resolve? "DT_RUNPATH" (← Dyntab.runpath? dyn))
  let relocs ← liftExcept (Reloc.locateAll view.segments rela jmprel)
  let symtab ← liftExcept (symtabRaw.mapM (Symbol.ofRaw strtab))
  let callTargets ←
    liftExcept (CallTargets.ofRaw view.segments view.header.e_entry initArrRaw finiArrRaw)
  return {
    header := view.header,
    segments := view.segments,
    symtab,
    needed,
    soname,
    runpath,
    relocs,
    callTargets }

end LeanLoad.Parse

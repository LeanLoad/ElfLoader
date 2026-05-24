/-
Checked ELF parse-stage product and runtime-file driver.
-/

import LeanLoad.Parse.DynMap.Basic
import LeanLoad.Parse.Reloc.Table
import LeanLoad.Parse.Symbol.Checked
import LeanLoad.Parse.Symbol.SysVHash
import LeanLoad.Parse.CallTargets
import LeanLoad.Parse.LoadMap.Basic
import LeanLoad.Parse.LoadMap.ProgramHeader.Basic
import LeanLoad.Runtime.File

namespace LeanLoad.Parse

open Runtime

/-- The checked form of an ELF.

    Construction enforces per-rela segment containment, checked symbol names, and
    callable target coverage. `Elf` keeps `fileSize` as a field rather than an
    index so heterogeneous files can live in one `Array Elf`; the indexed
    witnesses stay on the segment table and the structures that depend on it.
    Only downstream-consumed ELF-header facts are retained: `machine` selects
    psABI-specific relocation semantics, and `phdr*` carries the program-header
    table metadata needed for `AT_PHDR`. -/
structure Elf where
  fileSize : ByteSize
  /-- Target ISA / psABI (`e_machine`, gabi 02 § Machine), used to pick the
      relocation formula table. -/
  machine  : ElfMachine
  /-- Checked PT_LOAD array, in phdr order, with array-level
      ordering/disjointness witnessed. -/
  segments : SegmentTable fileSize
  /-- Program-header table file offset (`e_phoff`, gabi 02 § ELF Header). -/
  phdrOff : FileOff
  /-- Program-header count (`e_phnum`, gabi 02 § ELF Header). -/
  phdrCount : UInt16
  /-- Checked mapping from the program-header table to an ELF address for `AT_PHDR`.
      The table must be file-backed by a PT_LOAD; this pushes the runtime auxv
      precondition into parse. -/
  phdrMap : ProgramHeaderMap segments phdrOff (ProgramHeaderSize * phdrCount.toNat)
  symtab   : Array Symbol
  needed   : Array String
  soname   : Option String
  runpath  : Option String
  /-- Dynamic relocations located in their target segments. -/
  relocs   : Reloc.RelocTable segments
  /-- Checked `e_entry`, `DT_INIT_ARRAY`, and `DT_FINI_ARRAY` call targets.
      Each slot is zero or targets an executable PT_LOAD in `segments`. -/
  callTargets : CallTargets segments
  deriving Repr

private def parse [Monad m] (file : Runtime.File m)
    (range : FileRange file.size) (decoder : Decoder α) : ExceptT String m α := do
  liftExcept <| decoder.decode (← file.read range)

private def parseDynamicArray [Monad m] [Decodable α] (file : Runtime.File m)
    (tag : String) (loc : Option (FileRange file.size)) :
    ExceptT String m (Array α) := do
  match loc with
  | none => pure #[]
  | some range =>
      let bytes := range.size.toNat
      let entrySize := ByteSize.toNat (Decodable.byteSize (α := α))
      unless bytes % entrySize == 0 do
        throw s!"parse: {tag}: byte size {bytes} is not a multiple of {entrySize}"
      parse file range (Decodable.arrayDecoder (α := α) (bytes / entrySize))

/-- Parse `.dynsym` using `DT_HASH.nchain` as the symbol count. LeanLoad requires
    `DT_SYMTAB` and `DT_HASH` to appear together. -/
private def parseSymtab [Monad m] (file : Runtime.File m)
    (view : LoadMap file.size) (symtabLoc : Option Eaddr)
    (hashLoc : Option (FileRange file.size)) :
    ExceptT String m RawSymtab := do
  match symtabLoc, hashLoc with
  | none, none => pure #[]
  | some _, none => throw "parse: DT_SYMTAB present without DT_HASH"
  | none, some _ => throw "parse: DT_HASH present without DT_SYMTAB"
  | some symtabLoc, some hashLoc =>
      let hash : RawSysVHash ← parse file hashLoc Decodable.decoder
      if hash.symCount == 0 then
        return #[]
      let symRange ← liftExcept
        (LoadMap.fileRange view
          { start := symtabLoc
            size := ByteSize.ofEntries hash.symCount (Decodable.byteSize (α := RawSym)) })
      parse file symRange (Decodable.arrayDecoder (α := RawSym) hash.symCount)

/-- Checked parse over any file-like byte source. -/
def parseFile [Monad m] (file : Runtime.File m) : ExceptT String m Elf := do
  let fileSize := file.size
  let ⟨headerInBounds⟩ ← liftExcept <| require
    ((0 : FileOff).toNat + (ByteSize.ofNat ElfHeaderSize).toNat ≤ fileSize.toNat)
    s!"parse: ELF header at file offset 0x{(0 : FileOff).toNat} requested \
      {(ByteSize.ofNat ElfHeaderSize).toNat} bytes, past file size {fileSize.toNat}"
  let headerRange : FileRange fileSize :=
    { off := 0, size := ByteSize.ofNat ElfHeaderSize, inBounds := headerInBounds }
  let header : ElfHeader fileSize ← parse file headerRange (ElfHeader.decoder fileSize)
  let programHeaders ←
    parse file header.programHeaderRange
      (ProgramHeader.arrayDecoder fileSize header.e_phnum.toNat)
  let loadMap ← liftExcept (LoadMap.ofHeaders fileSize header programHeaders)
  let phdrNbytes := ProgramHeaderSize * loadMap.header.e_phnum.toNat
  let phdrMap ←
    liftExcept (ProgramHeaderMap.ofSegments loadMap.segments loadMap.header.e_phoff phdrNbytes)
  let locs : DynMap fileSize ← match programHeaders.find? (·.p_type == .dynamic) with
    | none => pure default
    | some ph =>
        parse file ph.fileRange (DynMap.decoder loadMap ph.fileRange.size)
  let strtab : Strtab := (← locs.strtab.mapM file.read).getD Strtab.empty
  let symtabRaw ← parseSymtab file loadMap locs.symtab locs.hash
  let rela ← parseDynamicArray (α := RawRela) file "DT_RELA" locs.rela
  let jmprel ← parseDynamicArray (α := RawRela) file "DT_JMPREL" locs.jmprel
  let initArrRaw ← parseDynamicArray (α := Eaddr) file "DT_INIT_ARRAY" locs.initArr
  let finiArrRaw ← parseDynamicArray (α := Eaddr) file "DT_FINI_ARRAY" locs.finiArr
  let needed ← liftExcept (locs.needed.mapM (strtab.resolve "DT_NEEDED"))
  let soname ← liftExcept (strtab.resolve? "DT_SONAME" locs.soname)
  let runpath ← liftExcept (strtab.resolve? "DT_RUNPATH" locs.runpath)
  let relocs ← liftExcept (Reloc.locateAll loadMap.segments rela jmprel)
  let symtab ← liftExcept (symtabRaw.mapM (Symbol.ofRaw strtab))
  let callTargets ←
    liftExcept (CallTargets.ofRaw loadMap.segments loadMap.header.e_entry initArrRaw finiArrRaw)
  return {
    fileSize
    machine := loadMap.header.e_machine,
    segments := loadMap.segments,
    phdrOff := loadMap.header.e_phoff,
    phdrCount := loadMap.header.e_phnum,
    phdrMap,
    symtab,
    needed,
    soname,
    runpath,
    relocs,
    callTargets }

/-- Pure checked parse over in-memory fixture bytes. -/
def parseByteArray (bytes : ByteArray) : Except String Elf :=
  (parseFile (Runtime.File.ofByteArray bytes)).run

end LeanLoad.Parse

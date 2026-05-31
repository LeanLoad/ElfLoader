import ElfLoader.Parse.DynMap.Raw
import ElfLoader.Parse.Symbol.Raw
import ElfLoader.Parse.Symbol.SysVHash
import ElfLoader.Parse.Reloc.Raw
import ElfLoader.Parse.LoadMap.Basic

/-!
`DynMap` construction from raw `.dynamic` entries.

`RawEntry` / `RawDyntab` stay in `DynMap.Raw`; this module is the parse-stage
interface that keeps string-table references as `.dynstr` offsets and resolves
dynamic ELF-address ranges through `LoadMap` to file ranges.

Spec: gabi 08 (`third_party/abi/gabi/docsrc/elf/08-dynamic.rst`).
-/

namespace ElfLoader.Parse

open Runtime

/-- Dynamic-table interpretation consumed by the checked parse driver.

String references stay as `.dynstr` offsets; address-like dynamic entries are
resolved to file byte ranges by combining the raw table with `LoadMap`. -/
structure DynMap (fileSize : ByteSize) where
  needed : Array StrtabOff
  soname : Option StrtabOff
  rpath : Option StrtabOff
  runpath : Option StrtabOff
  strtab  : Option (FileRange fileSize)
  symtab  : Option Eaddr
  hash    : Option (FileRange fileSize)
  rela    : Option (FileRange fileSize)
  jmprel  : Option (FileRange fileSize)
  initArr : Option (FileRange fileSize)
  finiArr : Option (FileRange fileSize)
  deriving Repr, Inhabited

namespace DynMap

/-- Resolve all dynamic-table facts that the rest of parse consumes. -/
def ofRawDyntab (tab : RawDyntab) (view : LoadMap fileSize) :
    Except String (DynMap fileSize) := do
  let needed :=
    (tab.findAll .needed).map (fun e => StrtabOff.mk e.d_un)
  let soname := (← tab.single? .soname).map StrtabOff.mk
  let rpath := (← tab.single? .rpath).map StrtabOff.mk
  let runpath := (← tab.single? .runpath).map StrtabOff.mk
  let strtab ← (← tab.rawRange? .strtab .strsz).mapM (LoadMap.fileRange view)
  let symtabRaw ← tab.single? .symtab
  match symtabRaw, ← tab.single? .syment with
  | some _, none => throw "parse: DT_SYMTAB present without DT_SYMENT"
  | _, some actual =>
      let expected := (Decodable.byteSize (α := RawSym)).toNat
      unless actual.toNat == expected do
        throw s!"parse: DT_SYMENT={actual.toNat}, expected {expected}"
  | _, none => pure ()
  let symtab := symtabRaw.map Eaddr.mk
  let hash : Option (FileRange fileSize) ←
    match symtab, ← tab.single? .hash with
    | none, none => pure none
    | some _, none => throw "parse: DT_SYMTAB present without DT_HASH"
    | none, some _ => throw "parse: DT_HASH present without DT_SYMTAB"
    | some _, some hash =>
        (LoadMap.fileRange view { start := Eaddr.mk hash, size := RawSysVHash.byteSize }).map some
  let relaRange ← tab.rawRange? .rela .relasz
  match relaRange, ← tab.single? .relaent with
  | some _, none => throw "parse: DT_RELA present without DT_RELAENT"
  | _, some actual =>
      let expected := (Decodable.byteSize (α := RawRela)).toNat
      unless actual.toNat == expected do
        throw s!"parse: DT_RELAENT={actual.toNat}, expected {expected}"
  | _, none => pure ()
  let rela ← relaRange.mapM (LoadMap.fileRange view)
  let jmprelRange ← tab.rawRange? .jmprel .pltrelsz
  let pltrel ← (← tab.single? .pltrel).mapM PltRelKind.ofRaw
  let jmprel : Option (FileRange fileSize) ←
    match jmprelRange, pltrel with
    | none, _ => pure none
    | some _, none => throw "parse: DT_JMPREL present without DT_PLTREL"
    | some _, some .rel => throw "parse: DT_PLTREL=DT_REL, expected DT_RELA"
    | some range, some .rela =>
        (LoadMap.fileRange view range).map some
  let initArr ← (← tab.rawRange? .initArray .initArraySz).mapM (LoadMap.fileRange view)
  let finiArr ← (← tab.rawRange? .finiArray .finiArraySz).mapM (LoadMap.fileRange view)
  return {
    needed
    soname
    rpath
    runpath
    strtab
    symtab
    hash
    rela
    jmprel
    initArr
    finiArr }

/-- Decode `.dynamic` bytes and resolve every parse-visible dynamic fact. -/
def decoder (view : LoadMap fileSize) (bytes : ByteSize) : Decoder (DynMap fileSize) := do
  let tab ← RawDyntab.decoder bytes
  match ofRawDyntab tab view with
  | .ok map => return map
  | .error e => throw e

end DynMap

end ElfLoader.Parse

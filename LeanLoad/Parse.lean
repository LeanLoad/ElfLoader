/-
Checked ELF parse-stage product and public parse entry points.
-/

import LeanLoad.Parse.Dynamic.InitFini
import LeanLoad.Parse.Dynamic.Reloc.Table
import LeanLoad.Parse.Dynamic.Symbol.Checked
import LeanLoad.Parse.Dynamic.Types
import LeanLoad.Parse.Driver
import LeanLoad.Parse.LoadMap.ElfHeader.Basic
import LeanLoad.Parse.LoadMap.SegmentTable.Basic
import LeanLoad.Runtime

namespace LeanLoad.Parse

/-- The checked form of an ELF.

    `Elf.ofDynamic` enforces per-rela segment containment, checked symbol
    names, and init/fini target coverage as preconditions on construction;
    the `Elf` type is the witness that those checks passed. Header policy,
    PT_LOAD well-formedness, and dynamic string resolution are already carried
    by `Dynamic`. -/
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
  relocs   : Dynamic.Reloc.RelocTable segments
  /-- `DT_INIT_ARRAY` entries — ctors, walked forward on startup. Each entry is
      zero or targets an executable PT_LOAD in `segments`. -/
  initArr  : Dynamic.InitFiniArray segments
  /-- `DT_FINI_ARRAY` entries — dtors, walked backward on exit. Each entry is
      zero or targets an executable PT_LOAD in `segments`. -/
  finiArr  : Dynamic.InitFiniArray segments
  deriving Repr

namespace Elf

/-- Check a dynamic staging image into the final witness-carrying `Elf`. -/
def ofDynamic (raw : Dynamic) : Except String Elf := do
  let header := raw.header
  let relocs ← Dynamic.Reloc.locateAll raw.segments raw.rela raw.jmprel
  let symtab : Array Symbol ← raw.symtab.mapM (Symbol.ofRaw raw.strtab)
  let initArr ← Dynamic.checkInitFiniArray "DT_INIT_ARRAY" raw.segments raw.initArr
  let finiArr ← Dynamic.checkInitFiniArray "DT_FINI_ARRAY" raw.segments raw.finiArr
  return {
    header,
    symtab,
    needed := raw.needed,
    soname := raw.soname,
    runpath := raw.runpath,
    segments := raw.segments,
    relocs,
    initArr,
    finiArr }

end Elf

/-- Monad-polymorphic checked parse. The `FileReader m` abstracts byte delivery;
    all parse and validation errors flow through `ExceptT`. -/
def parseM [Monad m] (r : FileReader m) : ExceptT String m Elf := do
  let image ← readStaging r
  match Elf.ofDynamic image with
  | .ok elf  => pure elf
  | .error e => throw e

/-- Production entry point: parse and check an open file. -/
def parse (f : Runtime.File) : IO Elf := do
  match ← (parseM (Runtime.fileReader f)).run with
  | .ok elf  => pure elf
  | .error e => throw (IO.userError e)

end LeanLoad.Parse

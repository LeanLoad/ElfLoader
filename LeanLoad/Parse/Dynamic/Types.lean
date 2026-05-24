/-
Transient dynamic staging image.

`Dynamic` is the parse-stage image after `.dynamic` pointers have been followed
through `LoadMap`, but before whole-ELF checks build the final `Elf`.
-/

import LeanLoad.Parse.Dynamic.Reloc.Raw
import LeanLoad.Parse.Dynamic.Strtab
import LeanLoad.Parse.Dynamic.Symbol.Raw
import LeanLoad.Parse.LoadMap.ElfHeader.Basic
import LeanLoad.Parse.LoadMap.SegmentTable.Basic

namespace LeanLoad.Parse

/-- Transient byte-decoded ELF. `Elf.ofDynamic` immediately checks this into
    `LeanLoad.Parse.Elf`, so downstream code consumes the witnessed type. -/
structure Dynamic where
  header  : ElfHeader
  segments : SegmentTable
  strtab  : Strtab
  symtab  : RawSymtab
  needed  : Array String
  soname  : Option String
  runpath : Option String
  rela    : Array RawRela
  jmprel  : Array RawRela
  initArr : Array Eaddr
  finiArr : Array Eaddr
  deriving Repr

end LeanLoad.Parse

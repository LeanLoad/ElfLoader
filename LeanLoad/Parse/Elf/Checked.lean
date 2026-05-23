/-
Checked ELF parse-stage product.
-/

import LeanLoad.Parse.Dynamic.Reloc.Checked
import LeanLoad.Parse.Dynamic.Symbol.Checked
import LeanLoad.Parse.Elf.InitFini
import LeanLoad.Parse.FileView.ElfHeader.Basic
import LeanLoad.Parse.FileView.SegmentTable.Basic

namespace LeanLoad.Parse

namespace Elf

/-- Dynamic relocations targeting one checked file-view segment. -/
structure Relocs (segment : Segment) where
  rela   : Array (Rela segment.eaddr segment.memsz)
  jmprel : Array (Rela segment.eaddr segment.memsz)
  deriving Repr

end Elf

/-- The checked form of an ELF.

    `Elf.ofDynamic` enforces ELF-class / endian sanity, gabi-07 PT_LOAD
    well-formedness, per-rela segment containment, and init/fini target
    coverage as preconditions on construction; the `Elf` type is the witness
    that those checks passed. -/
structure _root_.LeanLoad.Parse.Elf where
  /-- Parsed ELF header. `ElfHeader` is already semantically typed: magic,
      identifiers, `e_type`, `e_machine`, addresses, and sentinels are decoded
      to parse-layer field types. -/
  header   : _root_.LeanLoad.Parse.ElfHeader
  symtab   : Array _root_.LeanLoad.Parse.Symbol
  needed   : Array String
  soname   : Option String
  runpath  : Option String
  /-- Checked PT_LOAD array, in phdr order, with array-level
      ordering/disjointness witnessed. -/
  segments : _root_.LeanLoad.Parse.SegmentTable
  /-- Dynamic relocations indexed by their target segment. -/
  relocs   : (i : Fin segments.items.size) → Elf.Relocs segments.items[i]
  /-- `DT_INIT_ARRAY` entries — ctors, walked forward on startup. Each entry is
      zero or targets an executable PT_LOAD in `segments`. -/
  initArr  : Elf.InitFiniArray segments
  /-- `DT_FINI_ARRAY` entries — dtors, walked backward on exit. Each entry is
      zero or targets an executable PT_LOAD in `segments`. -/
  finiArr  : Elf.InitFiniArray segments

end LeanLoad.Parse

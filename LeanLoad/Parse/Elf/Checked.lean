/-
Checked ELF type: the parse-stage product consumed by Discover, Plan, and
Materialize.

`Elf` carries the loader-facing facts established during checked parse:
header policy, segment well-formedness, relocation containment, resolved
dynamic strings, and constructor/destructor target coverage.
-/

import LeanLoad.Parse.Ehdr.Basic
import LeanLoad.Parse.Symbol.Checked
import LeanLoad.Parse.Segment.Properties

namespace LeanLoad.Parse

namespace Elf

/-- A constructor/destructor function pointer that is zero or targets an
    executable PT_LOAD in `segments`. -/
abbrev InitFiniEntry (segments : Segments) :=
  { entry : Vaddr // callTargetInExecSeg segments entry }

/-- `DT_INIT_ARRAY` / `DT_FINI_ARRAY` entries. The array is ELF-owned
    because call order is table order, while each entry carries the
    witness that it targets an executable segment. -/
abbrev InitFiniArray (segments : Segments) :=
  Array (InitFiniEntry segments)

end Elf

/-- The checked form of an ELF.

    `parseM` enforces ELF-class / endian sanity, gabi-07 PT_LOAD
    well-formedness, and per-rela segment containment as preconditions on
    construction; the `Elf` type *is* the witness that those checks passed.

    Fields dropped from the byte-decoded staging image: `phdrs` (replaced by
    `segments.map (·.phdr)`), `dyn` (no post-parse consumer), and `strtab`
    (consumed at parse time to pre-resolve symbol and DT_NEEDED names). -/
structure Elf where
  /-- Parsed ELF header. `Ehdr` is already semantically typed: magic,
      identifiers, `e_type`, `e_machine`, addresses, and sentinels are decoded
      to parse-layer field types. -/
  header   : Ehdr
  symtab   : Array Symbol
  needed   : Array String
  soname   : Option String
  runpath  : Option String
  /-- Checked PT_LOAD array, in phdr order, with relas grouped by the segment
      they target and array-level ordering/disjointness witnessed. -/
  segments : Segments
  /-- `DT_INIT_ARRAY` entries — ctors, walked forward on startup. Each entry is
      zero or targets an executable PT_LOAD in `segments`. -/
  initArr  : Elf.InitFiniArray segments
  /-- `DT_FINI_ARRAY` entries — dtors, walked backward on exit. Each entry is
      zero or targets an executable PT_LOAD in `segments`. -/
  finiArr  : Elf.InitFiniArray segments
  deriving Repr

end LeanLoad.Parse

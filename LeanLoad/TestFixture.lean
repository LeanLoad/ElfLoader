/-
Shared synthetic-`ParsedElf` builders for compile-time `#guard` checks
in the planning stages. Each closure (and any single-use helper, e.g.
string-table packing) lives next to the `#guard`s that exercise it,
in `Plan/{Init,Resolve,Reloc/Aarch64}.lean`. Only the truly shared
constructors are exported here.

The IO integration tests under `LeanLoad.X.Test` still exercise the
real `examples/build/main` and remain authoritative for "the pipeline
copes with musl-gcc's actual output".
-/

import LeanLoad.Discover

namespace LeanLoad.Test

open LeanLoad
open LeanLoad.Parse
open LeanLoad.Discover

/-- Build a synthetic `ParsedElf` with all fields defaulted; override
    only the fields a test cares about. -/
def synthElf
    (needed  : Array String          := #[])
    (symtab  : Array Symbol.Symbol64 := #[])
    (strtab  : Symbol.StringTable    := ⟨#[]⟩)
    (rela    : Array Reloc.Rela64    := #[])
    (initArr : Array UInt64          := #[])
    : File.ParsedElf :=
  { (default : File.ParsedElf) with needed, symtab, strtab, rela, initArr }

/-- Build a synthetic `LoadedObject` (name + synthetic ELF). -/
def synthObj
    (name   : String)
    (needed : Array String          := #[])
    (symtab : Array Symbol.Symbol64 := #[])
    (strtab : Symbol.StringTable    := ⟨#[]⟩)
    (rela   : Array Reloc.Rela64    := #[])
    : LoadedObject :=
  { name
    path := s!"<synth:{name}>"
    elf  := synthElf (needed := needed) (symtab := symtab)
                     (strtab := strtab) (rela := rela) }

end LeanLoad.Test

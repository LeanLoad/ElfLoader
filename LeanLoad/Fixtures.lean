/-
Shared synthetic-`Elaborate.Elf` builders for compile-time `#guard`
checks across pipeline modules. Single-use helpers (e.g. string-table
packing) live next to the `#guard`s that exercise them, in
`{Layout,Resolve,Spec/Reloc/Aarch64}.lean`. Only the truly shared
constructors are exported here.

The IO integration tests in `LeanLoad/Test.lean` exercise the real
`examples/build/main` and remain authoritative for "the pipeline
copes with musl-gcc's actual output".
-/

import LeanLoad.Plan.Discover
import LeanLoad.Elaborate.Elf

namespace LeanLoad.Fixtures

open LeanLoad
open LeanLoad.Elaborate
open LeanLoad.Discover

/-- Build a synthetic `LoadedObject` (name + synthetic elaborated ELF).
    All ELF fields default; override only what a test cares about.
    Synthetic ELFs have no PT_LOAD segments, so the `segments` array
    is empty — well-formedness is vacuously true (the elaborated form
    is constructed directly without going through `elaborate`). -/
def synthObj
    (name   : String)
    (needed : Array String           := #[])
    (symtab : Array Elaborate.Symbol  := #[])
    : LoadedObject :=
  let elf : Elaborate.Elf :=
    { (default : Elaborate.Elf) with needed, symtab }
  { name, path := s!"<synth:{name}>", elf }

end LeanLoad.Fixtures

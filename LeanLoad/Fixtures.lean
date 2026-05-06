/-
Shared synthetic-`ParsedElf` builders for compile-time `#guard` checks
across pipeline modules. Single-use helpers (e.g. string-table
packing) live next to the `#guard`s that exercise them, in
`{Layout,Resolve,Spec/Reloc/Aarch64}.lean`. Only the truly shared
constructors are exported here.

The IO integration tests in `LeanLoad/Test.lean` exercise the real
`examples/build/main` and remain authoritative for "the pipeline
copes with musl-gcc's actual output".
-/

import LeanLoad.DiscoverPlan

namespace LeanLoad.Fixtures

open LeanLoad
open LeanLoad.Spec
open LeanLoad.Parse
open LeanLoad.Discover

/-- Build a synthetic `LoadedObject` (name + synthetic ELF). All ELF
    fields default; override only what a test cares about. -/
def synthObj
    (name   : String)
    (needed : Array String          := #[])
    (symtab : Array Symbol.Symbol64 := #[])
    (strtab : Spec.StringTable.StringTable    := ⟨#[]⟩)
    (rela   : Array Reloc.Rela64    := #[])
    : LoadedObject :=
  { name
    path := s!"<synth:{name}>"
    elf  := { (default : File.ParsedElf) with needed, symtab, strtab, rela } }

/-- Build a synthetic `DepGraph` from a list of objects, deriving
    `deps` via `Discover.buildDeps` (resolves each `needed` string
    against the canonical names of `objs`). -/
def synthDepGraph (objs : Array LoadedObject) : DepGraph :=
  { objects := objs, deps := buildDeps objs }

end LeanLoad.Fixtures

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

import LeanLoad.Plan.Discover

namespace LeanLoad.Fixtures

open LeanLoad
open LeanLoad.Spec
open LeanLoad.Parse
open LeanLoad.Discover

/-- Build a synthetic `LoadedObject` (name + synthetic ELF). All ELF
    fields default; override only what a test cares about. The
    `elf_wf` witness is discharged by `decide` — synthetic ELFs have
    no PT_LOAD segments (`phdrs = #[]`), so `WellFormed #[]` is
    vacuously true. -/
def synthObj
    (name   : String)
    (needed : Array String          := #[])
    (symtab : Array Symbol.Symbol64 := #[])
    (strtab : Spec.StringTable.StringTable    := ⟨#[]⟩)
    (rela   : Array Reloc.Rela64    := #[])
    : LoadedObject :=
  let elf : File.ParsedElf :=
    { (default : File.ParsedElf) with phdrs := #[], needed, symtab, strtab, rela }
  { name
    path := s!"<synth:{name}>"
    elf
    -- `elf.phdrs = #[]` ⇒ goal reduces to `WellFormed #[]`, discharged
    -- by the closed lemma `Parse.Segment.WellFormed_nil` (inline `decide`
    -- fails because synthObj's free parameters leave the goal open).
    elf_wf := Parse.Segment.WellFormed_nil }

end LeanLoad.Fixtures

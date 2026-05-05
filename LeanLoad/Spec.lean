/-
`LeanLoad.Spec` — single audit surface for what LeanLoad *is*.

A reader scanning this file sees every type, constant, and pure
function that defines the system's externally-visible behaviour.
The defs themselves live in their gabi-chapter files (one chapter
per file); this module re-exports them and indexes them by spec
area, so the reader does not have to grep the tree to know what's
in scope.

For *proven properties* about these specs, see `LeanLoad.Thm`.

Pipeline (input → output; all stages are pure unless marked IO):

  Parse        : ByteArray             → ParsedElf            (gabi 02-08)
  Discover IO  : Path                  → LinkMap              (gabi 08, ld.so)
  Resolve      : LinkMap               → ResolutionTable      (gabi 08)
  Layout       : LinkMap × init/fini   → LoaderPlan           (gabi 07)
  Init         : LinkMap               → init/fini orders     (gabi 08)
  ──────── all-pure planning to here; bases unknown ────────
  Materialize IO : Layouts             → Regions × Bases      (kernel mmap)
  Reloc        : LinkMap × bases × rt  → Array RelocWrite     (gabi 06, aarch64-elf-abi)
  Apply IO     : Writes                → mutated memory
  RunInits IO  : Bases × init order    → ctors called
  Exec IO      : entry, stack, auxv    → no return            (gabi 08 § Process Init)

Trust boundary:
- **Verified**: `Parse/`, `Plan/`, the search-path-resolution helpers
  in `Discover.lean`. Every `def` is total and the formula table is
  spec-faithful (theorems in `LeanLoad.Thm`).
- **Trusted**: the IO body of `Discover.discover`, all of `Load/`,
  `FFI/`, and `runtime/`. Audited by inspection.
-/

import LeanLoad.Parse
import LeanLoad.Plan
import LeanLoad.Discover

/-! ## ELF format (gabi 02–08, transcribed)

Types and constants below are direct transcriptions of the
System V Generic ABI; the def *is* the spec, with no second copy.

* `LeanLoad.Parse.Header.{Ident, ElfHeader64}` — gabi 02 § ELF Header.
  Constants: `ELFCLASS64`, `ELFDATA2LSB`, `ET_DYN`, `ET_EXEC`,
  `EM_AARCH64`.
* `LeanLoad.Parse.Program.{Header64}` — gabi 07 § Program Header.
  Constants: `PT_LOAD`, `PT_DYNAMIC`, `PF_R`, `PF_W`, `PF_X`.
* `LeanLoad.Parse.Dynamic.{Dyn64}` — gabi 08 § Dynamic Section.
  Constants: `DT_NEEDED`, `DT_STRTAB`, `DT_SYMTAB`, `DT_INIT_ARRAY`, …
* `LeanLoad.Parse.Symbol.{Symbol64, StringTable}` — gabi 04 § String
  Tables, gabi 05 § Symbol Tables. Constants: `STB_GLOBAL`, `STB_WEAK`,
  `STT_FUNC`, `SHN_UNDEF`.
* `LeanLoad.Parse.Reloc.{Rela64}` — gabi 06 § Relocation.
-/

/-! ## Pipeline data types

The values that flow between stages.

* `LeanLoad.Parse.File.ParsedElf` — output of `Parse`; one decoded ELF.
* `LeanLoad.Discover.{LoadedObject, LinkMap}` — output of `Discover`;
  transitive closure of `DT_NEEDED`, in BFS order.
* `LeanLoad.Plan.Resolve.{SymRef, Unresolved, ResolutionTable}` —
  output of `Resolve`.
* `LeanLoad.Plan.Layout.{Mapping, ObjectLayout, LoaderPlan}` — output
  of `Layout` + `Init` (combined plan).
* `LeanLoad.Plan.Reloc.{FormulaInputs, FormulaResult, RelocWrite,
  Bases, Formula}` — `Reloc` planner inputs/outputs and the per-arch
  formula type.
-/

/-! ## Pure pipeline functions (the spec is the impl)

These `def`s are both the implementation and the spec — there is no
abstract second copy. Every one is total (Lean elaborator certifies).

* `LeanLoad.Parse.File.parse` — `ByteArray → Except String ParsedElf`.
* `LeanLoad.Parse.File.vaToOffset` — VA → file offset within `PT_LOAD`.
  Soundness: `LeanLoad.Thm.vaToOffset_correct`.
* `LeanLoad.Discover.searchCandidates` — soname → candidate paths
  (LD_LIBRARY_PATH, RUNPATH, defaults; gabi 08).
* `LeanLoad.Plan.Resolve.{resolveByName, buildTable}` — symbol
  resolution (BFS over `LinkMap.objects`, gabi 08).
* `LeanLoad.Plan.Layout.{objectLayout, fromLinkMap}` — memory layout.
  Structural correctness: `LeanLoad.Thm.fromLinkMap_layouts_size`,
  `fromLinkMap_deterministic`.
* `LeanLoad.Plan.Init.{initOrder, finiOrder}` — DFS post-order
  traversal of dependencies; total via fuel-based recursion.
* `LeanLoad.Plan.Reloc.plan` — apply a `Formula` to every rela entry
  in the link map.
* `LeanLoad.Plan.Reloc.Aarch64.formula` — AArch64 relocation formula
  table (aarch64-elf-abi § Dynamic Relocations). Totality and
  width-validity: `LeanLoad.Thm.{formula_is_total, formula_size_valid}`.
-/

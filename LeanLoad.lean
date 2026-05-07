/-
Root of the `LeanLoad` library; re-exports every public module.

The pipeline is `Parse → Elaborate → Plan → Exec`. Parse is byte-decode
only (no semantic checks). Elaborate validates and enriches into a
typed form (Segment bundles, pre-resolved symbol names, etc.). Plan
emits planning data (layouts, patches, ctor lists). Exec is the IO
bookend that realizes plans against the runtime.

Each `Parse.*` module cites its gabi/abi section next to the type
definitions. Theorems live in `Thm/` and adjacent to their subjects.
-/
import LeanLoad.Parse.Structs
import LeanLoad.Parse.Dynamic
import LeanLoad.Parse.RawElf

import LeanLoad.Elaborate.Header
import LeanLoad.Elaborate.Strtab
import LeanLoad.Elaborate.Symbol
import LeanLoad.Elaborate.Segment
import LeanLoad.Elaborate.WellFormed
import LeanLoad.Elaborate.Reloc
import LeanLoad.Elaborate.Elf

import LeanLoad.Plan.Layout
import LeanLoad.Plan.Discover
import LeanLoad.Discover
import LeanLoad.Plan.Resolve
import LeanLoad.Plan.Reloc
import LeanLoad.Plan.Init
import LeanLoad.Exec
import LeanLoad.Runtime
import LeanLoad.Thm.Layout

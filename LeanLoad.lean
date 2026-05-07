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
import LeanLoad.Parse.Header
import LeanLoad.Parse.Program
import LeanLoad.Parse.Dynamic
import LeanLoad.Parse.StringTable
import LeanLoad.Parse.Symbol
import LeanLoad.Parse.Reloc
import LeanLoad.Parse.GnuHash
import LeanLoad.Parse.File

import LeanLoad.Elaborate.Segment
import LeanLoad.Elaborate.Reloc
import LeanLoad.Elaborate.Reloc.Aarch64
import LeanLoad.Elaborate.Reloc.X86_64
import LeanLoad.Elaborate.Reloc.Formula
import LeanLoad.Elaborate.File

import LeanLoad.Plan.Layout
import LeanLoad.Plan.Discover
import LeanLoad.Discover
import LeanLoad.Plan.Resolve
import LeanLoad.Plan.Reloc
import LeanLoad.Plan.Init
import LeanLoad.Exec
import LeanLoad.Runtime
import LeanLoad.Thm.Layout

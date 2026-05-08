/-
Root of the `LeanLoad` library; re-exports every public module.

The pipeline is `Parse → Elaborate → Plan → Exec`. Parse is byte-decode
only (no semantic checks). Elaborate validates and enriches into a
typed form (`Segment` with gabi-07 invariants and pre-discharged
page-arithmetic facts, pre-resolved symbol names, etc.). Plan emits
planning data (layouts with sorted-segments witness, patches with
`coversRela` witness, ctor lists). Exec is the IO bookend that
realizes plans against the runtime; reservation-relative `InRange`
bounds are discharged structurally from `Plan.Layout`'s
`bss_inRange` / `patch_inRange` so no runtime range check remains.

Each `Parse.*` module cites its gabi/abi section next to the type
definitions. Cross-stage theorems live alongside the constructions
they discharge (e.g. `Plan/Layout.lean`).
-/
import LeanLoad.Parse.Structs
import LeanLoad.Parse.Dynamic
import LeanLoad.Parse.RawElf

import LeanLoad.Elaborate.Header
import LeanLoad.Elaborate.Strtab
import LeanLoad.Elaborate.Symbol
import LeanLoad.Elaborate.Segment
import LeanLoad.Elaborate.Reloc
import LeanLoad.Elaborate.Elf

import LeanLoad.Runtime

import LeanLoad.Plan.Layout
import LeanLoad.Discover.Plan
import LeanLoad.Discover.IO
import LeanLoad.Plan.Resolve
import LeanLoad.Plan.Reloc
import LeanLoad.Plan.Realize
import LeanLoad.Plan.Init

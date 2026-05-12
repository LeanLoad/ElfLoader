/-
Root of the `LeanLoad` library; re-exports every public module.

Pipeline: `Parse → Elaborate → Discover → Plan → Materialize → Runtime`.

  • Parse — byte decode only (no semantic checks).
  • Elaborate — validate, enrich to typed `Elf` (with
    `segmentsNonOverlap` etc. as proof fields).
  • Discover — IO walk DT_NEEDED; produce non-empty `ObjectList`.
  • Plan — base-free planning: symbol resolution, init order,
    layout (`assignBases` / `totalSpan`).
  • Materialize — base-aware: build the `LoadOps` tree from the
    plan + IO-supplied reservation base, gate through the
    decidable safety check.
  • Runtime — `@[extern]` trust seam; `MemoryOp.runSafe` accepts
    only the safety-witnessed flat op array.
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

import LeanLoad.Discover.Plan
import LeanLoad.Discover.IO

import LeanLoad.Plan.Align
import LeanLoad.Plan.Layout
import LeanLoad.Plan.Resolve
import LeanLoad.Plan.Reloc
import LeanLoad.Plan.Init
import LeanLoad.Plan.Aggregate

import LeanLoad.Materialize.LoadOps
import LeanLoad.Materialize.Reloc
import LeanLoad.Materialize.BasedPlan
import LeanLoad.Materialize.Build

/-
Materialized op tree: `SegmentOps` / `ElfOps` / `LoadOps`.

Stage boundary:
  • `Plan/` produces base-free facts: `LoadPlan` (page math,
    `objectSpan`, `totalSpan`), `Resolve.Table`, `Reloc.LoadRelocs`,
    `Init.order`. None of those know an mmap base.
  • `Materialize/` consumes those plus the IO-supplied reservation
    base and emits this hierarchical tree of `MemoryOp`s, which
    `LoadOps.flatten` lowers to the flat array the runtime seam
    expects.

Hierarchy (each level owns the one below):
  • `SegmentOps` — one segment's plan + the ops targeting its
    address range (setup + reloc writes, in execution order).
  • `ElfOps`     — one elf's chosen base + its `SegmentOps`.
  • `LoadOps`    — list of `ElfOps` for every loaded object.

`setupOps` (below) builds the per-segment setup ops from a
`SegmentPlan` + base. `Materialize.bakeSegmentRelocs` (in
`Reloc.lean`) builds the per-segment reloc writes. `Build.build`
combines them into `SegmentOps`.

Flatten methods on each level fold downward to a flat
`Array MemoryOp`. The decidable safety check (`Materialize.safe`)
runs on the flattened array.
-/

import LeanLoad.Plan.Layout
import LeanLoad.Runtime

namespace LeanLoad.Materialize

open LeanLoad
open LeanLoad.Plan (SegmentPlan)

-- ============================================================================
-- Per-segment setup ops: mmapFile (if file-backed) + zeroout (if
-- partial-page BSS) + final mprotect. Reloc writes targeting this
-- segment live alongside in `SegmentOps.ops`.
-- ============================================================================

/-- Setup ops to materialize one segment's memory at the chosen base:

      • `mmapFile` for the file-backed prefix (if any), widened
        with `PROT_WRITE` so reloc patches can write before the
        final `mprotect`.
      • `zeroout` for the partial-page BSS (file overlay's tail
        past `filesz`). gabi BSS bytes inside the file overlay's
        last page aren't guaranteed zero — toolchains may leave
        non-zero data there.
      • `mprotect` over the whole segment range, setting final
        permissions. -/
def setupOps (handle : Runtime.FileHandle) (sp : SegmentPlan)
    (base : UInt64) : Array MemoryOp :=
  let absVaddr := base + sp.pageVaddr
  (if sp.hasFileBacked then
     #[.mmapFile handle absVaddr sp.fileOverlayLen
        (sp.prot ||| Runtime.PROT_WRITE) sp.fileOffset]
   else #[]) ++
  (if sp.hasPartialBss then
     #[.zeroout (absVaddr + sp.pageInset + sp.segment.filesz) sp.partialBssLen]
   else #[]) ++
  #[.mprotect absVaddr sp.pageLength sp.prot]

-- ============================================================================
-- Hierarchy: SegmentOps → ElfOps → LoadOps.
-- ============================================================================

/-- Per-segment ops bundle: the base-free plan + every op targeting
    this segment's address range (setup + reloc writes), in
    execution order. The setup-vs-writes distinction is captured at
    the op level (`IsOverlay` / `IsWrite` / `IsMprotect`). -/
structure SegmentOps where
  plan : SegmentPlan
  ops  : Array MemoryOp

/-- Per-elf ops: chosen base + per-segment ops bundles. -/
structure ElfOps where
  base     : UInt64
  segments : Array SegmentOps

/-- Top-level: list of per-elf bundles, in elf order (main is at index 0). -/
abbrev LoadOps := Array ElfOps

/-- Flatten one segment's ops. -/
def SegmentOps.flatten (so : SegmentOps) : Array MemoryOp := so.ops

/-- Flatten one elf's ops, segment by segment. -/
def ElfOps.flatten (eo : ElfOps) : Array MemoryOp :=
  eo.segments.foldl (init := #[]) fun acc so => acc ++ so.flatten

/-- Flatten the full load tree, elf by elf. -/
def LoadOps.flatten (lo : LoadOps) : Array MemoryOp :=
  lo.foldl (init := #[]) fun acc eo => acc ++ eo.flatten

end LeanLoad.Materialize

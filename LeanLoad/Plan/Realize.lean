/-
Realize planner — pure.

Hierarchical plan structure: each `RegionPlan` owns its setup ops
(mmapFile/zeroout/mprotect) AND its reloc writes (patches that target
this region's address range). Each `ObjectPlan` owns its
`RegionPlan`s. A `LoadPlan` is the list of `ObjectPlan`s.

Flat `Array MemoryOp` is recovered via `LoadPlan.flatten` for the
runtime-side `MemoryOp.runSafe`. The hierarchy stays intact through
the safety check, which decides over the flattened op list.

Layers:
  • `Region.ops`   — per-region setup ops (mmapFile/zeroout/mprotect).
  • `RegionPlan`   — region + setup ops + writes.
  • `ObjectPlan`   — base + regions for one elf.
  • `LoadPlan`     — list of objects.
  • `buildLoadPlan` — constructs the tree.
  • `planOps`      — flattens, runs decidable safety check.
-/

import LeanLoad.Plan.Layout
import LeanLoad.Plan.Reloc
import LeanLoad.Runtime

namespace LeanLoad.Realize

open LeanLoad
open LeanLoad.Layout (Region)
open LeanLoad.Elaborate (Elf Formula)

-- ============================================================================
-- Per-region realize ops (setup only; writes live alongside in RegionPlan).
-- ============================================================================

/-- Setup ops to materialize one `Region`'s memory:

      • `mmapFile` for the file-backed prefix (if any), widened
        with `PROT_WRITE` for reloc patches.
      • `zeroout` for the partial-page BSS (file overlay's tail
        past `filesz`).
      • `mprotect` over the whole segment range, setting final
        permissions.

    Reloc writes targeting this region are bundled separately in
    `RegionPlan.writeOps`. -/
def Region.ops (handle : Runtime.FileHandle) (r : Region) : Array MemoryOp :=
  (if r.hasFileBacked then
     #[.mmapFile handle r.absVaddr r.fileOverlayLen
        (r.prot ||| Runtime.PROT_WRITE) r.fileOffset]
   else #[]) ++
  (if r.hasPartialBss then
     #[.zeroout r.partialBssAddr r.partialBssLen]
   else #[]) ++
  #[.mprotect r.absVaddr r.length r.prot]

-- ============================================================================
-- Hierarchical plan: Segment → Elf → Load.
-- ============================================================================

/-- Per-segment plan: every op (setup + reloc writes) targeting this
    segment's address range, in execution order. The setup-vs-writes
    distinction is captured at the op level (`IsOverlay` /
    `IsWrite` / `IsMprotect`); structurally they live in one array. -/
structure SegmentPlan where
  region : Region
  ops    : Array MemoryOp

/-- Flatten a segment's plan — just the ops field. -/
def SegmentPlan.flatten (sp : SegmentPlan) : Array MemoryOp := sp.ops

/-- Per-elf plan: chosen base + per-segment plans. -/
structure ElfPlan where
  base     : UInt64
  segments : Array SegmentPlan

/-- Flatten an elf's plan to a flat op list (segment by segment). -/
def ElfPlan.flatten (ep : ElfPlan) : Array MemoryOp :=
  ep.segments.foldl (init := #[]) fun acc sp => acc ++ sp.flatten

/-- Top-level plan: list of elf plans. -/
abbrev LoadPlan := Array ElfPlan

/-- Flatten a load plan to a flat op list (elf by elf). -/
def LoadPlan.flatten (lp : LoadPlan) : Array MemoryOp :=
  lp.foldl (init := #[]) fun acc ep => acc ++ ep.flatten

-- ============================================================================
-- Builder.
-- ============================================================================

/-- Build the hierarchical plan from elfs + handles + bases + reloc
    inputs. Per segment of each elf, emits a `SegmentPlan` bundling
    setup ops and writes; per elf, an `ElfPlan` bundling segment plans. -/
def buildLoadPlan (elfs : Array Elf) (handles : Array Runtime.FileHandle)
    (h_size : handles.size = elfs.size)
    (bases : Array UInt64) (h_bases : bases.size = elfs.size)
    (formula : Formula) (rt : Resolve.Table elfs.size) :
    Except String LoadPlan := do
  let mut lp : Array ElfPlan := #[]
  for h : i in [:elfs.size] do
    let elf := elfs[i]
    let handle := handles[i]'(by rw [h_size]; exact h.upper)
    let base := bases[i]'(by rw [h_bases]; exact h.upper)
    let mut segments : Array SegmentPlan := #[]
    for h2 : segI in [:elf.segments.size] do
      let segIdx : Fin elf.segments.size := ⟨segI, h2.upper⟩
      let seg := elf.segments[segIdx]
      let region : Region := { base, seg }
      let setupOps := Region.ops handle region
      let writeOps ← Reloc.planSegmentWrites formula elfs bases h_bases rt
        ⟨i, h.upper⟩ seg region
      segments := segments.push { region, ops := setupOps ++ writeOps }
    lp := lp.push { base, segments }
  return lp

-- ============================================================================
-- Full op list: flatten the LoadPlan and gate through a decidable
-- safety check.
-- ============================================================================

/-- Flatten the LoadPlan and check safety. The hierarchical structure
    of `LoadPlan` makes the disjointness intent clear (each region
    owns its writes; each object owns its regions); the dynamic
    `decide` confirms it on the actual op array. -/
def planOps (rsvAddr rsvLen : UInt64) (lp : LoadPlan) :
    Except String { ops : Array MemoryOp //
      OverlaysDisjoint ops ∧
      OverlaysContained rsvAddr rsvLen ops ∧
      WritesContained rsvAddr rsvLen ops ∧
      MprotectsContained rsvAddr rsvLen ops } :=
  let ops := lp.flatten
  if h : OverlaysDisjoint ops ∧
         OverlaysContained rsvAddr rsvLen ops ∧
         WritesContained rsvAddr rsvLen ops ∧
         MprotectsContained rsvAddr rsvLen ops then
    .ok ⟨ops, h⟩
  else
    .error "planOps: planned ops violate safety invariants \
      (loader bug — overlays collide or extend outside the \
      reservation)"

end LeanLoad.Realize

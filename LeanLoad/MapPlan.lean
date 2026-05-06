/-
Map planner — pure.

Per-object plan: an `ObjectLayout` plus the `PerObjectOp`s derived
from its segments. The hierarchical shape means `MapApply` iterates
one object at a time with the reservation directly in scope —
no `Array (Option Region)` accumulator needed.

Per-object op order (preserved by emission and required by apply):

  1. (Implicit) anon `MAP_FIXED` reservation at `[layout.base,
     layout.base + layout.span)`. Always exactly one per object;
     not a constructor — apply does this unconditionally before
     the per-object op loop.
  2. For each segment:
     - `overlay` — file-backed `MAP_PRIVATE | MAP_FIXED` at
                   `layout.base + s.vaddr` for `s.fileLenPaged` bytes.
     - `bssZero` — clear partial-last-page BSS (skip if memsz=filesz).
  3. For each segment: `mprotect` — drop the temporary `PROT_WRITE`.
-/

import LeanLoad.DiscoverPlan
import LeanLoad.Layout
import LeanLoad.Runtime

namespace LeanLoad.Map

open LeanLoad
open LeanLoad.Layout
open LeanLoad.Parse.Segment

-- ============================================================================
-- PerObjectOp — operations performed inside one object's reservation
-- ============================================================================

/-- One mmap-stage operation, scoped to a single object's reservation.
    The "which object" is encoded by the enclosing `ObjectPlan` —
    no `objectIdx` field per op. -/
inductive PerObjectOp where
  /-- File-backed `MAP_PRIVATE | MAP_FIXED` overlay at `addr` with the
      given `prot` and file offset. `segIdx` indexes into the object's
      `layout.segments` (so apply can place the resulting `Region` in
      the right slot). -/
  | overlay  (segIdx : Nat) (addr : UInt64) (len : USize)
             (fileOff : UInt64) (prot : UInt32)
  /-- Clear partial-last-page BSS bytes inside the object's reservation. -/
  | bssZero  (offset : USize) (len : USize)
  /-- `mprotect` a sub-range of the object's reservation. -/
  | mprotect (offset : USize) (len : USize) (prot : UInt32)
  deriving Repr

/-- Per-object plan: a layout and its derived ops. The reservation
    `[layout.base, layout.base + layout.span)` is implicit (apply
    always reserves before running ops). -/
structure ObjectPlan where
  layout : ObjectLayout
  ops    : Array PerObjectOp
  deriving Repr

-- ============================================================================
-- Plan
-- ============================================================================

/-- Plan one object's ops from its layout. -/
private def planObject (lyt : ObjectLayout) : ObjectPlan := Id.run do
  let mut ops : Array PerObjectOp := #[]
  for h : i in [:lyt.segments.size] do
    let s := lyt.segments[i]
    if s.fileLenPaged > 0 then
      let writableProt := s.prot ||| Runtime.PROT_WRITE
      ops := ops.push (.overlay i (lyt.base + s.vaddr)
                                s.fileLenPaged.toUSize
                                s.fileOffsetPaged
                                writableProt)
    let bssLen := s.phdr.p_memsz - s.fileLen
    if bssLen > 0 then
      let bssOff := (s.vaddr + s.pageInset + s.fileLen).toUSize
      ops := ops.push (.bssZero bssOff bssLen.toNat.toUSize)
  for s in lyt.segments do
    ops := ops.push (.mprotect s.vaddr.toUSize s.length.toUSize s.prot)
  return { layout := lyt, ops }

/-- Plan all mmap operations for a process, grouped by object. -/
def plan (layouts : Array ObjectLayout) : Array ObjectPlan :=
  layouts.map planObject

end LeanLoad.Map

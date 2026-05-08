/-
Realize planner — pure.

Joins the upstream pure planners (`Layout`, `Reloc`, `Init`) into a
single `Array MemoryOp` describing every kernel call the loader will
make. The IO bookend (`Main.realize`) is a thin wrapper that calls
`MemoryOp.runAll ops`, then runs the one-shot finalizers (stack
alloc + `execAndJump`).

Three layers:

  - `Region.ops`   — per-region: anon reserve + file overlay (if
                     any) + partial-page zero (if any) + final
                     mprotect.
  - `realizeOps`   — all regions across all elfs.
  - `planOps`      — realize ops ++ Reloc patches.

All three are pure; tests `#guard` against the emitted op list.
-/

import LeanLoad.Plan.Layout
import LeanLoad.Runtime

namespace LeanLoad.Realize

open LeanLoad
open LeanLoad.Layout (Region)
open LeanLoad.Elaborate (Elf)

-- ============================================================================
-- Per-region realize ops.
-- ============================================================================

/-- Ops to realize one `Region` from a file: anon reserve + file
    overlay (if any) + partial-page zero (if any) + final mprotect.
    Step order matches glibc/musl's loader. -/
def Region.ops (handle : Runtime.FileHandle) (r : Region) : Array MemoryOp :=
  let ops : Array MemoryOp := #[.mmapAnon r.absVaddr r.length]
  let ops := if r.hasFileBacked then
    ops.push (.mmapFile handle r.absVaddr r.fileOverlayLen
                (r.prot ||| Runtime.PROT_WRITE) r.fileOffset)
  else ops
  let ops := if r.hasPartialBss then
    ops.push (.zeroout r.partialBssAddr r.partialBssLen)
  else ops
  ops.push (.mprotect r.absVaddr r.length r.prot)

-- ============================================================================
-- All-regions realize.
-- ============================================================================

/-- Realize ops for every elf's segments, in elf order. -/
def realizeOps (elfs : Array Elf) (handles : Array Runtime.FileHandle)
    (h_size : handles.size = elfs.size)
    (bases : Array UInt64) (h_bases : bases.size = elfs.size) :
    Array MemoryOp := Id.run do
  let mut ops : Array MemoryOp := #[]
  for h : i in [:elfs.size] do
    let elf := elfs[i]
    let handle := handles[i]'(by rw [h_size]; exact h.upper)
    let base := bases[i]'(by rw [h_bases]; exact h.upper)
    for seg in elf.segments do
      ops := ops ++ Region.ops handle ⟨base, seg⟩
  return ops

-- ============================================================================
-- Full op list: realize ++ patches. Ctors are user-code execution
-- (not kernel-state ops) and run inline from `Main.realize` after
-- `MemoryOp.runAll` finishes.
-- ============================================================================

/-- The full op list — what `Main.realize` runs through
    `MemoryOp.runAll`. -/
def planOps (elfs : Array Elf) (handles : Array Runtime.FileHandle)
    (h_size : handles.size = elfs.size)
    (bases : Array UInt64) (h_bases : bases.size = elfs.size)
    (patches : Array MemoryOp) : Array MemoryOp :=
  realizeOps elfs handles h_size bases h_bases ++ patches

end LeanLoad.Realize

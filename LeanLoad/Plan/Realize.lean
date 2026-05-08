/-
Realize planner — pure.

Joins the upstream pure planners (`Layout`, `Reloc`, `Init`) into a
single `Array (RuntimeOp elfs.size)` describing every kernel call
the loader will make. `RuntimeOp` is parameterised by the number
of file handles available at IO time; `mmapFile`'s `fileIdx :
Fin elfs.size` indexes into the IO-side `handles` table totally.

The IO bookend (`Main.realize`) is a thin wrapper that calls
`RuntimeOp.runAll handles h_size ops`, then runs the one-shot
finalizers (stack alloc + `execAndJump`).

Three layers:

  - `Region.ops`   — per-region: anon reserve + file overlay (if
                     any) + partial-page zero (if any) + final
                     mprotect.
  - `realizeOps`   — all regions across all elfs.
  - `planOps`      — realize ops ++ Reloc patches ++ ctor calls
                     — the full op list `Main.realize` consumes.

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

/-- Ops to realize one `Region`: anon reserve + file overlay (if
    any) + partial-page zero (if any) + final mprotect. The
    `fileIdx` is the position of the elf in the IO-time handle
    table; `runAll` resolves it. -/
def Region.ops {n : Nat} (fileIdx : Fin n) (r : Region) : Array (RuntimeOp n) :=
  let ops : Array (RuntimeOp n) := #[.mmapAnon r.absVaddr r.length]
  let ops := if r.hasFileBacked then
    ops.push (.mmapFile fileIdx r.absVaddr r.fileOverlayLen
                (r.prot ||| Runtime.PROT_WRITE) r.fileOffset)
  else ops
  let ops := if r.hasPartialBss then
    ops.push (.zeroout r.partialBssAddr r.partialBssLen)
  else ops
  ops.push (.mprotect r.absVaddr r.length r.prot)

-- ============================================================================
-- All-regions realize.
-- ============================================================================

/-- Realize ops for every elf's segments, in elf order. The loop
    index `i` doubles as the `fileIdx` for emitted `mmapFile` ops. -/
def realizeOps (elfs : Array Elf) (bases : Array UInt64)
    (h_bases : bases.size = elfs.size) :
    Array (RuntimeOp elfs.size) := Id.run do
  let mut ops : Array (RuntimeOp elfs.size) := #[]
  for h : i in [:elfs.size] do
    let elf := elfs[i]
    let base := bases[i]'(by rw [h_bases]; exact h.upper)
    for seg in elf.segments do
      ops := ops ++ Region.ops ⟨i, h.upper⟩ ⟨base, seg⟩
  return ops

-- ============================================================================
-- Full op list: realize ++ patches ++ ctors.
-- ============================================================================

/-- The full op list — what `Main.realize` runs through
    `RuntimeOp.runAll`. -/
def planOps (elfs : Array Elf) (bases : Array UInt64)
    (h_bases : bases.size = elfs.size)
    (patches : Array (RuntimeOp elfs.size)) (ctorAddrs : Array UInt64) :
    Array (RuntimeOp elfs.size) :=
  let ops := realizeOps elfs bases h_bases
  let ops := ops ++ patches
  ops ++ ctorAddrs.map (.callCtor ·)

end LeanLoad.Realize

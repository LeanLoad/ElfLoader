/-
Realize planner — pure.

Reserve-then-overlay design (kernel-picked reservation):

The IO bookend (`Main.realize`) calls `Runtime.mmapAnonAlloc
totalSpan` to get a kernel-picked anon block, then runs pure
planning inside that reservation:

  Per PT_LOAD segment:
    • `mmapFile` overlay for the file-backed prefix (with PROT_WRITE
       widened so reloc patches can write).
    • `zeroout` for the partial-page tail past `filesz` (kernel
       maps file content there, not zero).
    • `mprotect` over the segment range, setting final perms.

`planOps` concatenates `realizeOps` with reloc patches and gates
the result through a decidable safety check parameterized on the
reservation range.
-/

import LeanLoad.Plan.Layout
import LeanLoad.Runtime

namespace LeanLoad.Realize

open LeanLoad
open LeanLoad.Layout (Region)
open LeanLoad.Elaborate (Elf)

-- ============================================================================
-- Per-region realize ops. Lives inside the kernel-picked reservation;
-- the reservation itself isn't in the op array.
-- ============================================================================

/-- Ops to realize one `Region` inside the reservation:

      • `mmapFile` for the file-backed prefix (if any), widened
        with `PROT_WRITE` for reloc patches.
      • `zeroout` for the partial-page BSS (file overlay's tail
        past `filesz`).
      • `mprotect` over the whole segment range, setting final
        perms. The reservation underneath is `PROT_READ | PROT_WRITE`,
        so BSS pages start RW; this mprotect adjusts to the
        segment's final perm. -/
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
-- All-regions realize.
-- ============================================================================

/-- Realize ops for every elf, per segment in elf order. The
    kernel-picked reservation is set up in IO before this runs;
    every op here lives inside it. -/
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
-- Full op list: realize ++ patches, gated by a decidable safety
-- check parameterized on the reservation range.
-- ============================================================================

/-- The full op list for a kernel-picked reservation `[rsvAddr,
    rsvAddr + rsvLen)`. Returned subtype carries proofs that
    overlays don't collide and every overlay / write / mprotect
    lies inside the reservation. Planner bugs surface as `.error`. -/
def planOps (rsvAddr rsvLen : UInt64)
    (elfs : Array Elf) (handles : Array Runtime.FileHandle)
    (h_size : handles.size = elfs.size)
    (bases : Array UInt64) (h_bases : bases.size = elfs.size)
    (patches : Array MemoryOp) :
    Except String { ops : Array MemoryOp //
      OverlaysDisjoint ops ∧
      OverlaysContained rsvAddr rsvLen ops ∧
      WritesContained rsvAddr rsvLen ops ∧
      MprotectsContained rsvAddr rsvLen ops } :=
  let ops := realizeOps elfs handles h_size bases h_bases ++ patches
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

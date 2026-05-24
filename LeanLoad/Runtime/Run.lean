/-
Runtime interpreter for finalized load operations.

`Finalize` constructs an intrinsic-safe `LoadOps` tree without doing IO. This
module interprets that tree through the concrete C-backed memory effects, in
protocol order.
-/

import LeanLoad.Runtime.Memory
import LeanLoad.Finalize.LoadOps

namespace LeanLoad.Runtime

/-- Run one segment's intrinsic-safe ops in protocol order. -/
def runSegmentOps (so : Finalize.SegmentOps rsvAddr rsvLen objCount) : IO Unit := do
  if let some mmap := so.mmap then
    Memory.mmapFile mmap.handle mmap.addr mmap.len mmap.prot mmap.offset
  if let some z := so.zero then
    Memory.zero z.addr z.len
  for s in so.stores do
    Memory.store s.addr s.size s.value
  Memory.mprotect so.mprotect.addr so.mprotect.len so.mprotect.prot

/-- Run an intrinsic-safe op tree in protocol order. The safety proof fields are
    erased; runtime behaviour is plain per-op dispatch through `Runtime.Memory`. -/
def runLoadOps (lo : Finalize.LoadOps rsvAddr rsvLen objCount) : IO Unit :=
  lo.elfs.forM fun eo => eo.segments.forM runSegmentOps

end LeanLoad.Runtime

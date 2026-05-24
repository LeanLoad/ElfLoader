/-
Runtime interpreter for finalized load operations.

`Finalize` constructs an intrinsic-safe `LoadOps` tree without doing IO. This
module interprets that tree through an explicit `Memory` capability, in
protocol order.
-/

import LeanLoad.Runtime.Memory
import LeanLoad.Finalize.LoadOps

namespace LeanLoad.Runtime

/-- Run one segment's intrinsic-safe ops in protocol order. -/
def runSegmentOps [Monad m] (ops : Memory m)
    (so : Finalize.SegmentOps rsvAddr rsvLen objCount) : m Unit := do
  if let some mmap := so.mmap then
    ops.mmapFile mmap.handle mmap.addr mmap.len mmap.prot mmap.offset
  if let some z := so.zero then
    ops.zero z.addr z.len
  for s in so.stores do
    ops.store s.addr s.size s.value
  ops.mprotect so.mprotect.addr so.mprotect.len so.mprotect.prot

/-- Run an intrinsic-safe op tree in protocol order. The safety proof fields are
    erased; runtime behaviour is plain per-op dispatch through `ops`. -/
def runLoadOps [Monad m] (ops : Memory m)
    (lo : Finalize.LoadOps rsvAddr rsvLen objCount) : m Unit :=
  lo.elfs.forM fun eo => eo.segments.forM (runSegmentOps ops)

end LeanLoad.Runtime

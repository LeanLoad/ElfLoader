/-
Runtime interpreter for finalized load operations.

`Finalize` constructs an intrinsic-safe `LoadOps` tree without doing IO. This
module interprets that tree through the concrete C-backed memory effects, in
protocol order. The plan stores filesystem paths on each `MmapOp`; an
ambient `Runtime.Filesystem IO` is consulted to resolve each path back into
an open `Runtime.File` immediately before the mmap syscall.
-/

import ElfLoader.Runtime.Memory
import ElfLoader.Runtime.Filesystem
import ElfLoader.Finalize.LoadOps

namespace ElfLoader.Runtime

/-- Run one segment's intrinsic-safe ops in protocol order. The filesystem
    seam resolves each `MmapOp.path` to an open `File`; a `none` here means
    the path the planner recorded is no longer reachable. -/
def runSegmentOps (fs : Filesystem IO) (so : Finalize.SegmentOps rsvAddr rsvLen objCount) :
    IO Unit := do
  if let some mmap := so.mmap then
    match ← fs.openPath mmap.path with
    | none =>
        throw (IO.userError s!"Runtime.runSegmentOps: cannot open '{mmap.path}' for mmap")
    | some file =>
        Memory.mmapFile file mmap.addr mmap.len mmap.prot mmap.offset
  if let some z := so.zero then
    Memory.zero z.addr z.len
  for s in so.stores do
    Memory.store s.addr s.size s.value
  Memory.mprotect so.mprotect.addr so.mprotect.len so.mprotect.prot

/-- Run an intrinsic-safe op tree in protocol order. The safety proof fields are
    erased; runtime behaviour is plain per-op dispatch through `Runtime.Memory`,
    with paths resolved through `fs` exactly once per mmap. -/
def runLoadOps (fs : Filesystem IO) (lo : Finalize.LoadOps rsvAddr rsvLen objCount) :
    IO Unit :=
  lo.elfs.forM fun eo => eo.segments.forM (runSegmentOps fs)

end ElfLoader.Runtime

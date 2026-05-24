/-
Structural safety witness + IO interpreter.

The `SegmentSafe` / `ElfSafe` / `LoadSafe` predicates mirror the
`SegmentOps` / `ElfOps` / `LoadOps` tree structure. `BoundPlan`'s
per-(i, j) bound theorems map directly onto their fields, so
`Exec.build` constructs a witness inline with the tree
without ever materialising a flat predicate.

`runSafe` is the trust seam: it takes a `LoadSafe`-witnessed tree
and dispatches each op to the matching FFI primitive, in protocol
order (mmap → zero → stores → mprotect, per segment; segments
in-order per elf; elves in-order top-level). The witness fields are
erased at runtime — they exist only to gate the call.
-/

import LeanLoad.Exec
import LeanLoad.Exec.LoadOps

namespace LeanLoad.Exec

open LeanLoad

-- ============================================================================
-- IO interpreter — dispatches each op in protocol order.
-- ============================================================================

private def SegmentOps.runUnsafe (so : SegmentOps objCount) : IO Unit := do
  if let some m := so.mmap then m.run
  if let some z := so.zero then z.run
  for s in so.stores do s.run
  so.mprotect.run

private def LoadOps.runUnsafe (lo : LoadOps objCount) : IO Unit :=
  lo.elfs.forM fun eo => eo.segments.forM SegmentOps.runUnsafe

/-- Interpret a `LoadSafe`-witnessed layout tree. The witness fields
    are erased; IO behaviour is identical to a plain per-op
    dispatch. -/
def LoadOps.runSafe (rsvAddr rsvLen : UInt64)
    (lo : { lo : LoadOps objCount // LoadSafe rsvAddr rsvLen lo }) : IO Unit :=
  LoadOps.runUnsafe lo.val

end LeanLoad.Exec

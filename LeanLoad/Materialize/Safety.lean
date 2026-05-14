/-
Structural safety witness + IO interpreter.

The `SegmentSafe` / `ElfSafe` / `LoadSafe` predicates mirror the
`SegmentOps` / `ElfOps` / `LoadOps` tree structure. `BoundPlan`'s
per-(i, j) bound theorems map directly onto their fields, so
`Materialize.build` constructs a witness inline with the tree
without ever materialising a flat predicate.

`runSafe` is the trust seam: it takes a `LoadSafe`-witnessed tree
and dispatches each slot to the matching FFI primitive, in protocol
order (mmap → zero → stores → mprotect, per segment; segments
in-order per elf; elves in-order top-level). The witness fields are
erased at runtime — they exist only to gate the call.
-/

import LeanLoad.Materialize.LoadOps

namespace LeanLoad.Materialize

open LeanLoad

-- ============================================================================
-- Structural safety witness — mirrors the LoadOps tree shape.
-- ============================================================================

/-- Per-segment safety: every emitted slot fits inside the reservation. -/
structure SegmentSafe (rsvAddr rsvLen : UInt64) (so : SegmentOps n) : Prop where
  mmapInRange     : ∀ m, so.mmap = some m → Runtime.InRange m.addr m.len rsvAddr rsvLen
  zeroInRange     : ∀ z, so.zero = some z → Runtime.InRange z.addr z.len rsvAddr rsvLen
  storesInRange   : ∀ s ∈ so.stores, Runtime.InRange s.addr s.byteLen rsvAddr rsvLen
  mprotectInRange : Runtime.InRange so.mprotect.addr so.mprotect.len rsvAddr rsvLen

/-- Per-elf safety: every segment is SegmentSafe, plus within-elf mmap
    disjointness. -/
structure ElfSafe (rsvAddr rsvLen : UInt64) (eo : ElfOps n) : Prop where
  segments : ∀ k, ∀ h : k < eo.segments.size,
    SegmentSafe rsvAddr rsvLen (eo.segments[k]'h)
  mmapsDisjoint : ∀ i j, ∀ hi : i < eo.segments.size, ∀ hj : j < eo.segments.size,
    i < j → ∀ m_i m_j,
    (eo.segments[i]'hi).mmap = some m_i →
    (eo.segments[j]'hj).mmap = some m_j →
    Runtime.Disjoint m_i.addr m_i.len m_j.addr m_j.len

/-- Top-level structural safety: every elf is ElfSafe, plus cross-elf
    mmap disjointness. The natural target of the build's safety
    proof: `BoundPlan`'s per-slot and disjointness theorems map
    directly onto its fields. -/
structure LoadSafe (rsvAddr rsvLen : UInt64) (lo : LoadOps n) : Prop where
  elfs : ∀ k, ∀ h : k < lo.size, ElfSafe rsvAddr rsvLen (lo[k]'h)
  mmapsDisjoint : ∀ i j, ∀ hi : i < lo.size, ∀ hj : j < lo.size, i < j →
    ∀ k_i k_j (h_ki : k_i < (lo[i]'hi).segments.size)
              (h_kj : k_j < (lo[j]'hj).segments.size) m_i m_j,
    ((lo[i]'hi).segments[k_i]'h_ki).mmap = some m_i →
    ((lo[j]'hj).segments[k_j]'h_kj).mmap = some m_j →
    Runtime.Disjoint m_i.addr m_i.len m_j.addr m_j.len

-- ============================================================================
-- IO interpreter — dispatches each slot in protocol order.
-- ============================================================================

private def SegmentOps.runUnsafe (so : SegmentOps n) : IO Unit := do
  if let some m := so.mmap then m.run
  if let some z := so.zero then z.run
  for s in so.stores do s.run
  so.mprotect.run

private def LoadOps.runUnsafe (lo : LoadOps n) : IO Unit :=
  lo.forM fun eo => eo.segments.forM SegmentOps.runUnsafe

/-- Interpret a `LoadSafe`-witnessed layout tree. The witness fields
    are erased; IO behaviour is identical to a plain per-slot
    dispatch. -/
def LoadOps.runSafe (rsvAddr rsvLen : UInt64)
    (lo : { lo : LoadOps n // LoadSafe rsvAddr rsvLen lo }) : IO Unit :=
  LoadOps.runUnsafe lo.val

end LeanLoad.Materialize

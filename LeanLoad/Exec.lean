/-
Exec stage public interface.

Exec is the base-aware stage: it takes pure relocation/layout output plus the
IO-supplied reservation and emits an intrinsic-safe tree of runtime operations.

Public model:
  · `BoundPlan` — relocation/layout facts bound to a concrete reservation.
  · `SegmentSetup`, `SegmentOps`, `ElfOps`, `LoadOps` — the structured op tree.
    Safety witnesses live on the op tree itself, so invalid runtime op trees are
    not representable.

Implementation lives under `LeanLoad/Exec/`: `BoundPlan.lean` proves the
reservation bounds consumed by `Build.lean`, `LoadOps.lean` computes setup ops
and interprets the intrinsic-safe tree, `Reloc.lean` bakes relocation stores,
and `Build.lean` constructs the full witnessed tree.
-/

import LeanLoad.Exec.Range
import LeanLoad.Layout
import LeanLoad.Reloc
import LeanLoad.Runtime

namespace LeanLoad.Exec

open LeanLoad
open LeanLoad.Layout (SegmentLayout)

-- ============================================================================
-- BoundPlan — pure plan bound to an IO reservation.
-- ============================================================================

/-- The pure-pipeline `Reloc.Result` plus `Layout.Layout`, extended with the
    IO-supplied reservation, plus the coherence proof threaded from
    `Reserve.run`'s subtype. Every exec-stage consumer (`build`, `ctorAddrs`,
    `Main.realize`) takes a `BoundPlan` and accesses its planning fields
    directly via inheritance. -/
structure BoundPlan extends Reloc.Result where
  layout  : Layout.Layout graph.objects.size
  rsv     : Reserve
  h_total : rsv.len = layout.totalSpan

-- ============================================================================
-- LoadOps tree — structured runtime operation plan.
-- ============================================================================

/-- The three setup ops for one segment: file overlay (`mmap`),
    partial-page BSS clear (`zero`), and final permission (`mprotect`).
    `mmap` and `zero` are `Option`-typed because they may be skipped
    (BSS-only segments have no mmap; segments aligned to a page
    boundary have no partial BSS). `mprotect` is mandatory. The
    relocation stores are computed separately and added when extending
    to a full `SegmentOps`. -/
structure SegmentSetup where
  mmap     : Option MmapOp
  zero     : Option ZeroOp
  mprotect : MprotectOp

/-- Per-segment ops bundle: extends `SegmentSetup` (the three setup-time
    ops) with the underlying layout and the baked relocation stores.
    `setupSegment` produces the parent `SegmentSetup`; `bakeSegmentRelocs`
    produces `stores`; `Exec.buildSegment` combines them via
    `{ setup with layout, stores }`. -/
structure SegmentOps (rsvAddr rsvLen : UInt64) (objCount : Nat) extends SegmentSetup where
  layout   : SegmentLayout objCount
  stores   : Array StoreOp
  mmapInRange     : ∀ m, mmap = some m → Range.InRange m.addr m.len rsvAddr rsvLen
  zeroInRange     : ∀ z, zero = some z → Range.InRange z.addr z.len rsvAddr rsvLen
  storesInRange   : ∀ s ∈ stores, Range.InRange s.addr s.byteLen rsvAddr rsvLen
  mprotectInRange : Range.InRange mprotect.addr mprotect.len rsvAddr rsvLen

/-- Per-elf ops: just the per-segment ops bundles. The per-elf base
    address is implicit in each segment's op records (`MmapOp.addr`,
    `StoreOp.addr`, etc.) — those carry absolute addresses computed
    via `setupSegment` with the base mixed in. The source-of-truth
    base lives on `BoundPlan.bases[i]` for callers that need it
    (e.g. `Exec.ctorAddrs`, `Main.debug`). -/
structure ElfOps (rsvAddr rsvLen : UInt64) (objCount : Nat) where
  segments : Array (SegmentOps rsvAddr rsvLen objCount)
  mmapsDisjoint : ∀ i j, ∀ hi : i < segments.size, ∀ hj : j < segments.size,
    i < j → ∀ m_i m_j,
    (segments[i]'hi).mmap = some m_i →
    (segments[j]'hj).mmap = some m_j →
    Range.Disjoint m_i.addr m_i.len m_j.addr m_j.len

/-- Top-level op bundle, in elf order (main is at index 0). -/
structure LoadOps (rsvAddr rsvLen : UInt64) (objCount : Nat) where
  elfs : Array (ElfOps rsvAddr rsvLen objCount)
  mmapsDisjoint : ∀ i j, ∀ hi : i < elfs.size, ∀ hj : j < elfs.size, i < j →
    ∀ k_i k_j (h_ki : k_i < (elfs[i]'hi).segments.size)
              (h_kj : k_j < (elfs[j]'hj).segments.size) m_i m_j,
    ((elfs[i]'hi).segments[k_i]'h_ki).mmap = some m_i →
    ((elfs[j]'hj).segments[k_j]'h_kj).mmap = some m_j →
    Range.Disjoint m_i.addr m_i.len m_j.addr m_j.len
end LeanLoad.Exec

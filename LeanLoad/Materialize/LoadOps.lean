/-
Materialized op tree: `SegmentOps n` / `ElfOps n` / `LoadOps n` over
the typed slot records (`MmapSlot` / `ZeroSlot` / `StoreSlot` / `MprotectSlot`)
defined in `Runtime`.

Stage boundary:
  • `Plan/` produces base-free facts: `Layout n` (page math,
    `objectSpan`, `totalSpan`, per-segment relocs), `Resolve.Table`,
    `Init.order`. None of those know an mmap base.
  • `Materialize/` consumes those plus the IO-supplied reservation
    base and emits the structured op tree below. The runtime seam
    (`runSafe`) consumes the witnessed tree directly — there is no
    flat `Array` intermediate.

The natural number parameter `n` is the elf count, threaded through
from `SegmentLayout n` (for the per-segment `Entry n`s).

Per-segment shape (the "realize protocol"):
  1. *MmapSlot* — `Option MmapSlot` — `mmapFile` for the file-backed prefix,
     with `PROT_WRITE` widened so reloc stores can land before the
     final `mprotect`. Absent for BSS-only segments.
  2. *Zero* — `Option ZeroSlot` — clears the partial-page BSS tail past
     `filesz`, where the file overlay maps non-zero file bytes.
  3. *Stores* — `Array StoreSlot` — one per applicable relocation.
  4. *MprotectSlot* — mandatory — flips final permissions over the whole
     segment range.

Hierarchy:
  • `SegmentOps n` — one segment's plan + its 4 typed slots.
  • `ElfOps n`     — one elf's chosen base + its `SegmentOps`.
  • `LoadOps n`    — list of `ElfOps` for every loaded object.

Safety witness: `LoadSafe` mirrors the tree structure
(`SegmentSafe` per slot, `ElfSafe` per elf, `LoadSafe` across the
layout) and is built constructively by `Materialize.build` from
`BoundPlan`'s per-(i, j) `InRange` / `Disjoint` theorems. There is
no separate flat predicate — `runSafe` consumes a `LoadSafe`
witness directly.
-/

import LeanLoad.Plan.Layout
import LeanLoad.Runtime

namespace LeanLoad.Materialize

open LeanLoad
open LeanLoad.Plan (SegmentLayout)

-- ============================================================================
-- Hierarchy: SegmentOps n → ElfOps n → LoadOps n.
-- ============================================================================

/-- Per-segment ops bundle: the base-free plan + the 4 typed slots
    for the segment-realize protocol. -/
structure SegmentOps (n : Nat) where
  plan     : SegmentLayout n
  mmap     : Option MmapSlot
  zero     : Option ZeroSlot
  stores   : Array StoreSlot
  mprotect : MprotectSlot

/-- Per-elf ops: chosen base + per-segment ops bundles. -/
structure ElfOps (n : Nat) where
  base     : UInt64
  segments : Array (SegmentOps n)

/-- Top-level: array of per-elf bundles, in elf order (main is at index 0). -/
abbrev LoadOps (n : Nat) := Array (ElfOps n)

-- ============================================================================
-- Construction helper — compute the setup slots from a SegmentLayout.
-- Reloc stores are added separately by `Materialize.bakeSegmentRelocs`.
-- ============================================================================

/-- Setup slots (mmap, zero, mprotect) for one segment at the chosen
    base. The mmap is widened with `PROT_WRITE` so reloc stores can
    land before `mprotect` flips to final perms. -/
def setupSlots (sp : SegmentLayout n) (handle : Runtime.FileHandle)
    (base : UInt64) :
    Option MmapSlot × Option ZeroSlot × MprotectSlot :=
  let absVaddr := base + sp.pageVaddr
  let mmap : Option MmapSlot :=
    if sp.hasFileBacked then
      some { handle, addr := absVaddr, len := sp.fileOverlayLen,
             prot := sp.prot ||| Runtime.PROT_WRITE,
             offset := sp.fileOffset }
    else none
  let zero : Option ZeroSlot :=
    if sp.hasPartialBss then
      some { addr := absVaddr + sp.pageInset + sp.segment.filesz,
             len := sp.partialBssLen }
    else none
  let mprotect : MprotectSlot :=
    { addr := absVaddr, len := sp.pageLength, prot := sp.prot }
  (mmap, zero, mprotect)

-- ============================================================================
-- `setupSlots` characterisation. The four slot positions are simple
-- closed forms of `(base, sp)`; these lemmas extract them so the
-- `SegmentSafe` construction below can invoke the matching
-- `BoundPlan.segment_*_in_rsv` theorem directly.
-- ============================================================================

/-- The mmap slot, when present, sits at `base + sp.pageVaddr` of
    length `sp.fileOverlayLen`. -/
theorem setupSlots_mmap_eq (sp : SegmentLayout n) (handle : Runtime.FileHandle)
    (base : UInt64) (m : MmapSlot) (h : (setupSlots sp handle base).1 = some m) :
    m.addr = base + sp.pageVaddr ∧ m.len = sp.fileOverlayLen := by
  unfold setupSlots at h
  simp only at h
  by_cases h_fb : sp.hasFileBacked
  · rw [if_pos h_fb] at h
    injection h with h_eq
    rw [← h_eq]; exact ⟨rfl, rfl⟩
  · rw [if_neg h_fb] at h; cases h

/-- The zero slot, when present, sits at
    `base + sp.pageVaddr + sp.pageInset + sp.segment.filesz` of length
    `sp.partialBssLen`. -/
theorem setupSlots_zero_eq (sp : SegmentLayout n) (handle : Runtime.FileHandle)
    (base : UInt64) (z : ZeroSlot) (h : (setupSlots sp handle base).2.1 = some z) :
    z.addr = base + sp.pageVaddr + sp.pageInset + sp.segment.filesz ∧
    z.len = sp.partialBssLen := by
  unfold setupSlots at h
  simp only at h
  by_cases h_pb : sp.hasPartialBss
  · rw [if_pos h_pb] at h
    injection h with h_eq
    rw [← h_eq]; exact ⟨rfl, rfl⟩
  · rw [if_neg h_pb] at h; cases h

/-- The mprotect slot always sits at `base + sp.pageVaddr` of length
    `sp.pageLength`. -/
theorem setupSlots_mprotect_eq (sp : SegmentLayout n) (handle : Runtime.FileHandle)
    (base : UInt64) :
    (setupSlots sp handle base).2.2.addr = base + sp.pageVaddr ∧
    (setupSlots sp handle base).2.2.len = sp.pageLength := by
  exact ⟨rfl, rfl⟩

-- ============================================================================
-- Slot collectors — diagnostic-only. Walk the tree and gather one
-- slot kind. `Main.debug` prints their sizes for visibility; the
-- safety witness chain does not consume them.
-- ============================================================================

namespace LoadOps

/-- Every mmap across every elf and segment, in tree-walk order. -/
def mmaps (lo : LoadOps n) : Array MmapSlot :=
  lo.flatMap fun eo => eo.segments.filterMap (·.mmap)

/-- Every zero across every elf and segment. -/
def zeros (lo : LoadOps n) : Array ZeroSlot :=
  lo.flatMap fun eo => eo.segments.filterMap (·.zero)

/-- Every store across every elf and segment. -/
def stores (lo : LoadOps n) : Array StoreSlot :=
  lo.flatMap fun eo => eo.segments.flatMap (·.stores)

/-- Every mprotect across every elf and segment. -/
def mprotects (lo : LoadOps n) : Array MprotectSlot :=
  lo.flatMap fun eo => eo.segments.map (·.mprotect)

end LoadOps

-- ============================================================================
-- Structural safety witness: `SegmentSafe` / `ElfSafe` / `LoadSafe`
-- mirror the LoadOps tree. `BoundPlan`'s per-(i, j) bound theorems
-- map directly onto their fields, so `Materialize.build` constructs
-- a witness inline with the tree without ever materialising a flat
-- predicate. `runSafe` consumes a `LoadSafe`-witnessed value.
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

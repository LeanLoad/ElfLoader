/-
Materialized op tree: `SegmentOps n` / `ElfOps n` / `LoadOps n` over
the typed slot records (`MmapOp` / `ZeroOp` / `StoreOp` / `MprotectOp`)
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
  1. *MmapOp* — `Option MmapOp` — `mmapFile` for the file-backed prefix,
     with `PROT_WRITE` widened so reloc stores can land before the
     final `mprotect`. Absent for BSS-only segments.
  2. *Zero* — `Option ZeroOp` — clears the partial-page BSS tail past
     `filesz`, where the file overlay maps non-zero file bytes.
  3. *Stores* — `Array StoreOp` — one per applicable relocation.
  4. *MprotectOp* — mandatory — flips final permissions over the whole
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
-- Hierarchy: SegmentSetup + (layout, stores) → SegmentOps n → ElfOps n → LoadOps n.
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
    produces `stores`; `Materialize.buildSegment` combines them via
    `{ setup with layout, stores }`. -/
structure SegmentOps (n : Nat) extends SegmentSetup where
  layout   : SegmentLayout n
  stores   : Array StoreOp

/-- Per-elf ops: chosen base + per-segment ops bundles. -/
structure ElfOps (n : Nat) where
  base     : UInt64
  segments : Array (SegmentOps n)

/-- Top-level: array of per-elf bundles, in elf order (main is at index 0). -/
abbrev LoadOps (n : Nat) := Array (ElfOps n)

-- ============================================================================
-- Construction helper — compute the setup ops from a SegmentLayout.
-- Reloc stores are added separately by `Materialize.bakeSegmentRelocs`.
-- ============================================================================

/-- Compute the setup slots for one segment at the chosen base. The
    mmap is widened with `PROT_WRITE` so reloc stores can land before
    `mprotect` flips to final perms. -/
def setupSegment (sp : SegmentLayout n) (handle : Runtime.FileHandle)
    (base : UInt64) : SegmentSetup :=
  let absVaddr := base + sp.pageVaddr
  { mmap :=
      if sp.hasFileBacked then
        some { handle, addr := absVaddr, len := sp.fileOverlayLen,
               prot := sp.prot ||| Runtime.PROT_WRITE,
               offset := sp.fileOffset }
      else none
    zero :=
      if sp.hasPartialBss then
        some { addr := absVaddr + sp.pageInset + sp.segment.filesz,
               len := sp.partialBssLen }
      else none
    mprotect := { addr := absVaddr, len := sp.pageLength, prot := sp.prot } }

-- ============================================================================
-- `setupSegment` characterisation. The three slot positions are simple
-- closed forms of `(base, sp)`; these lemmas extract them so the
-- `SegmentSafe` construction below can invoke the matching
-- `BoundPlan.segment_*_in_rsv` theorem directly.
-- ============================================================================

/-- The mmap slot, when present, sits at `base + sp.pageVaddr` of
    length `sp.fileOverlayLen`. -/
theorem setupSegment_mmap_eq (sp : SegmentLayout n) (handle : Runtime.FileHandle)
    (base : UInt64) (m : MmapOp) (h : (setupSegment sp handle base).mmap = some m) :
    m.addr = base + sp.pageVaddr ∧ m.len = sp.fileOverlayLen := by
  unfold setupSegment at h
  simp only at h
  by_cases h_fb : sp.hasFileBacked
  · rw [if_pos h_fb] at h
    injection h with h_eq
    rw [← h_eq]; exact ⟨rfl, rfl⟩
  · rw [if_neg h_fb] at h; cases h

/-- The zero slot, when present, sits at
    `base + sp.pageVaddr + sp.pageInset + sp.segment.filesz` of length
    `sp.partialBssLen`. -/
theorem setupSegment_zero_eq (sp : SegmentLayout n) (handle : Runtime.FileHandle)
    (base : UInt64) (z : ZeroOp) (h : (setupSegment sp handle base).zero = some z) :
    z.addr = base + sp.pageVaddr + sp.pageInset + sp.segment.filesz ∧
    z.len = sp.partialBssLen := by
  unfold setupSegment at h
  simp only at h
  by_cases h_pb : sp.hasPartialBss
  · rw [if_pos h_pb] at h
    injection h with h_eq
    rw [← h_eq]; exact ⟨rfl, rfl⟩
  · rw [if_neg h_pb] at h; cases h

/-- The mprotect slot always sits at `base + sp.pageVaddr` of length
    `sp.pageLength`. -/
theorem setupSegment_mprotect_eq (sp : SegmentLayout n) (handle : Runtime.FileHandle)
    (base : UInt64) :
    (setupSegment sp handle base).mprotect.addr = base + sp.pageVaddr ∧
    (setupSegment sp handle base).mprotect.len = sp.pageLength := by
  exact ⟨rfl, rfl⟩

-- ============================================================================
-- Slot collectors — diagnostic-only. Walk the tree and gather one
-- slot kind. `Main.debug` prints their sizes for visibility; the
-- safety witness chain does not consume them.
-- ============================================================================

namespace LoadOps

/-- Every mmap across every elf and segment, in tree-walk order. -/
def mmaps (lo : LoadOps n) : Array MmapOp :=
  lo.flatMap fun eo => eo.segments.filterMap (·.mmap)

/-- Every zero across every elf and segment. -/
def zeros (lo : LoadOps n) : Array ZeroOp :=
  lo.flatMap fun eo => eo.segments.filterMap (·.zero)

/-- Every store across every elf and segment. -/
def stores (lo : LoadOps n) : Array StoreOp :=
  lo.flatMap fun eo => eo.segments.flatMap (·.stores)

/-- Every mprotect across every elf and segment. -/
def mprotects (lo : LoadOps n) : Array MprotectOp :=
  lo.flatMap fun eo => eo.segments.map (·.mprotect)

end LoadOps

-- The structural safety witness (`SegmentSafe` / `ElfSafe` / `LoadSafe`)
-- and the IO interpreter (`runSafe`) live in `Materialize/Safety.lean`,
-- which depends on the types defined here.

end LeanLoad.Materialize

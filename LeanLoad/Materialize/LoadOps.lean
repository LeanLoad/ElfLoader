/-
Materialized op tree: `SegmentOps n` / `ElfOps n` / `LoadOps n` over
the typed slot records (`Mmap` / `Zero` / `Store` / `Mprotect`)
defined in `Runtime`.

Stage boundary:
  • `Plan/` produces base-free facts: `LoadPlan n` (page math,
    `objectSpan`, `totalSpan`, per-segment relocs), `Resolve.Table`,
    `Init.order`. None of those know an mmap base.
  • `Materialize/` consumes those plus the IO-supplied reservation
    base and emits the structured op tree below. The runtime seam
    (`runSafe`) consumes the witnessed tree directly — there is no
    flat `Array` intermediate.

The natural number parameter `n` is the elf count, threaded through
from `SegmentPlan n` (for the per-segment `RelocEntry n`s).

Per-segment shape (the "realize protocol"):
  1. *Mmap* — `Option Mmap` — `mmapFile` for the file-backed prefix,
     with `PROT_WRITE` widened so reloc stores can land before the
     final `mprotect`. Absent for BSS-only segments.
  2. *Zero* — `Option Zero` — clears the partial-page BSS tail past
     `filesz`, where the file overlay maps non-zero file bytes.
  3. *Stores* — `Array Store` — one per applicable relocation.
  4. *Mprotect* — mandatory — flips final permissions over the whole
     segment range.

Hierarchy:
  • `SegmentOps n` — one segment's plan + its 4 typed slots.
  • `ElfOps n`     — one elf's chosen base + its `SegmentOps`.
  • `LoadOps n`    — list of `ElfOps` for every loaded object.

Safety predicates (`MmapsDisjoint`, `MmapsContained`,
`ZerosContained`, `StoresContained`, `MprotectsContained`) live on
`LoadOps` and are decidable; `safe` (in `Build.lean`) runs them to
produce the witness `runSafe` consumes.
-/

import LeanLoad.Plan.Layout
import LeanLoad.Runtime

namespace LeanLoad.Materialize

open LeanLoad
open LeanLoad.Plan (SegmentPlan)

-- ============================================================================
-- Hierarchy: SegmentOps n → ElfOps n → LoadOps n.
-- ============================================================================

/-- Per-segment ops bundle: the base-free plan + the 4 typed slots
    for the segment-realize protocol. -/
structure SegmentOps (n : Nat) where
  plan     : SegmentPlan n
  mmap     : Option Mmap
  zero     : Option Zero
  stores   : Array Store
  mprotect : Mprotect

/-- Per-elf ops: chosen base + per-segment ops bundles. -/
structure ElfOps (n : Nat) where
  base     : UInt64
  segments : Array (SegmentOps n)

/-- Top-level: array of per-elf bundles, in elf order (main is at index 0). -/
abbrev LoadOps (n : Nat) := Array (ElfOps n)

-- ============================================================================
-- Construction helper — compute the setup slots from a SegmentPlan.
-- Reloc stores are added separately by `Materialize.bakeSegmentRelocs`.
-- ============================================================================

/-- Setup slots (mmap, zero, mprotect) for one segment at the chosen
    base. The mmap is widened with `PROT_WRITE` so reloc stores can
    land before `mprotect` flips to final perms. -/
def setupSlots (sp : SegmentPlan n) (handle : Runtime.FileHandle)
    (base : UInt64) :
    Option Mmap × Option Zero × Mprotect :=
  let absVaddr := base + sp.pageVaddr
  let mmap : Option Mmap :=
    if sp.hasFileBacked then
      some { handle, addr := absVaddr, len := sp.fileOverlayLen,
             prot := sp.prot ||| Runtime.PROT_WRITE,
             offset := sp.fileOffset }
    else none
  let zero : Option Zero :=
    if sp.hasPartialBss then
      some { addr := absVaddr + sp.pageInset + sp.segment.filesz,
             len := sp.partialBssLen }
    else none
  let mprotect : Mprotect :=
    { addr := absVaddr, len := sp.pageLength, prot := sp.prot }
  (mmap, zero, mprotect)

-- ============================================================================
-- Slot collectors: walk the tree and gather one slot kind. Used by
-- the safety predicates below.
-- ============================================================================

namespace LoadOps

/-- Every mmap across every elf and segment. -/
def mmaps (lo : LoadOps n) : Array Mmap :=
  lo.foldl (init := #[]) fun acc eo =>
    eo.segments.foldl (init := acc) fun acc so =>
      match so.mmap with
      | some m => acc.push m
      | none   => acc

/-- Every zero across every elf and segment. -/
def zeros (lo : LoadOps n) : Array Zero :=
  lo.foldl (init := #[]) fun acc eo =>
    eo.segments.foldl (init := acc) fun acc so =>
      match so.zero with
      | some z => acc.push z
      | none   => acc

/-- Every store across every elf and segment. -/
def stores (lo : LoadOps n) : Array Store :=
  lo.foldl (init := #[]) fun acc eo =>
    eo.segments.foldl (init := acc) fun acc so => acc ++ so.stores

/-- Every mprotect across every elf and segment. -/
def mprotects (lo : LoadOps n) : Array Mprotect :=
  lo.foldl (init := #[]) fun acc eo =>
    eo.segments.foldl (init := acc) fun acc so => acc.push so.mprotect

end LoadOps

-- ============================================================================
-- Safety predicates over the structured tree.
-- Together they assert: file mmaps don't collide with each other,
-- and every slot lies inside the reservation `[rsvAddr, +rsvLen)`.
-- ============================================================================

/-- File mmaps are pairwise disjoint. -/
def MmapsDisjoint (lo : LoadOps n) : Prop :=
  let ms := lo.mmaps
  ∀ i, ∀ _ : i < ms.size, ∀ j, ∀ _ : j < ms.size, i < j →
    Runtime.Disjoint ms[i].addr ms[i].len ms[j].addr ms[j].len

/-- Every mmap lies inside the reservation. -/
def MmapsContained (rsvAddr rsvLen : UInt64) (lo : LoadOps n) : Prop :=
  let ms := lo.mmaps
  ∀ i, ∀ _ : i < ms.size,
    Runtime.InRange ms[i].addr ms[i].len rsvAddr rsvLen

/-- Every zero lies inside the reservation. -/
def ZerosContained (rsvAddr rsvLen : UInt64) (lo : LoadOps n) : Prop :=
  let zs := lo.zeros
  ∀ i, ∀ _ : i < zs.size,
    Runtime.InRange zs[i].addr zs[i].len rsvAddr rsvLen

/-- Every relocation store lies inside the reservation. -/
def StoresContained (rsvAddr rsvLen : UInt64) (lo : LoadOps n) : Prop :=
  let ss := lo.stores
  ∀ i, ∀ _ : i < ss.size,
    Runtime.InRange ss[i].addr ss[i].byteLen rsvAddr rsvLen

/-- Every mprotect lies inside the reservation. -/
def MprotectsContained (rsvAddr rsvLen : UInt64) (lo : LoadOps n) : Prop :=
  let ms := lo.mprotects
  ∀ i, ∀ _ : i < ms.size,
    Runtime.InRange ms[i].addr ms[i].len rsvAddr rsvLen

instance (lo : LoadOps n) : Decidable (MmapsDisjoint lo) := by
  unfold MmapsDisjoint; infer_instance

instance (rsvAddr rsvLen : UInt64) (lo : LoadOps n) :
    Decidable (MmapsContained rsvAddr rsvLen lo) := by
  unfold MmapsContained; infer_instance

instance (rsvAddr rsvLen : UInt64) (lo : LoadOps n) :
    Decidable (ZerosContained rsvAddr rsvLen lo) := by
  unfold ZerosContained; infer_instance

instance (rsvAddr rsvLen : UInt64) (lo : LoadOps n) :
    Decidable (StoresContained rsvAddr rsvLen lo) := by
  unfold StoresContained; infer_instance

instance (rsvAddr rsvLen : UInt64) (lo : LoadOps n) :
    Decidable (MprotectsContained rsvAddr rsvLen lo) := by
  unfold MprotectsContained; infer_instance

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

/-- Interpret a safety-witnessed load tree, given the reservation
    range that bounds every slot. The witness fields are erased; the
    IO behaviour is identical to a plain per-slot dispatch. -/
def LoadOps.runSafe (rsvAddr rsvLen : UInt64)
    (lo : { lo : LoadOps n //
      MmapsDisjoint lo ∧
      MmapsContained rsvAddr rsvLen lo ∧
      ZerosContained rsvAddr rsvLen lo ∧
      StoresContained rsvAddr rsvLen lo ∧
      MprotectsContained rsvAddr rsvLen lo }) : IO Unit :=
  LoadOps.runUnsafe lo.val

end LeanLoad.Materialize

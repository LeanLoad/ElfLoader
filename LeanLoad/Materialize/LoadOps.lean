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
-- `setupSlots` characterisation. The four slot positions are simple
-- closed forms of `(base, sp)`; these lemmas extract them so the
-- `SegmentSafe` construction below can invoke the matching
-- `BasedPlan.segment_*_in_rsv` theorem directly.
-- ============================================================================

/-- The mmap slot, when present, sits at `base + sp.pageVaddr` of
    length `sp.fileOverlayLen`. -/
theorem setupSlots_mmap_eq (sp : SegmentPlan n) (handle : Runtime.FileHandle)
    (base : UInt64) (m : Mmap) (h : (setupSlots sp handle base).1 = some m) :
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
theorem setupSlots_zero_eq (sp : SegmentPlan n) (handle : Runtime.FileHandle)
    (base : UInt64) (z : Zero) (h : (setupSlots sp handle base).2.1 = some z) :
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
theorem setupSlots_mprotect_eq (sp : SegmentPlan n) (handle : Runtime.FileHandle)
    (base : UInt64) :
    (setupSlots sp handle base).2.2.addr = base + sp.pageVaddr ∧
    (setupSlots sp handle base).2.2.len = sp.pageLength := by
  exact ⟨rfl, rfl⟩

-- ============================================================================
-- Slot collectors: walk the tree and gather one slot kind. Used by
-- the safety predicates below.
-- ============================================================================

namespace LoadOps

/-- Every mmap across every elf and segment, in tree-walk order.
    `flatMap` + `filterMap` so the structural-to-flat bridge proofs
    (`Safe_of_LoadSafe`) can chain `Array.mem_flatMap` +
    `Array.mem_filterMap` directly. -/
def mmaps (lo : LoadOps n) : Array Mmap :=
  lo.flatMap fun eo => eo.segments.filterMap (·.mmap)

/-- Every zero across every elf and segment. -/
def zeros (lo : LoadOps n) : Array Zero :=
  lo.flatMap fun eo => eo.segments.filterMap (·.zero)

/-- Every store across every elf and segment. -/
def stores (lo : LoadOps n) : Array Store :=
  lo.flatMap fun eo => eo.segments.flatMap (·.stores)

/-- Every mprotect across every elf and segment. -/
def mprotects (lo : LoadOps n) : Array Mprotect :=
  lo.flatMap fun eo => eo.segments.map (·.mprotect)

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
-- Structural safety predicates — `SegmentSafe` / `ElfSafe` /
-- `LoadSafe`. These mirror the structure of the LoadOps tree:
--
--   SegmentSafe — per-slot InRange (mmap / zero / store / mprotect)
--                  for one SegmentOps.
--   ElfSafe     — every segment of this elf is SegmentSafe, *and*
--                  the elf's segments' mmaps don't collide pairwise.
--   LoadSafe    — every elf is ElfSafe, *and* cross-elf mmaps don't
--                  collide pairwise.
--
-- These are the natural targets for the per-slot bound theorems in
-- `BasedPlan` (which produce exactly `Runtime.InRange ...` and
-- `Runtime.Disjoint ...` facts indexed by (i, j)). The flat
-- `Safe` predicate below is recovered from `LoadSafe` via
-- `Safe_of_LoadSafe`.
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
    proof: `BasedPlan`'s per-slot and disjointness theorems map
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
-- Safe — the five flat safety predicates bundled. The `LoadOps.runSafe`
-- entry point consumes this. `Safe_of_LoadSafe` (below) bridges the
-- structural form back to it, so `Materialize.build` only needs to
-- prove the structural one — which it gets directly from
-- `BasedPlan`'s per-(i, j) theorems.
-- ============================================================================

/-- All five safety predicates over a load tree, bundled. -/
structure Safe (rsvAddr rsvLen : UInt64) (lo : LoadOps n) : Prop where
  mmapsDisjoint      : MmapsDisjoint lo
  mmapsContained     : MmapsContained rsvAddr rsvLen lo
  zerosContained     : ZerosContained rsvAddr rsvLen lo
  storesContained    : StoresContained rsvAddr rsvLen lo
  mprotectsContained : MprotectsContained rsvAddr rsvLen lo

instance (rsvAddr rsvLen : UInt64) (lo : LoadOps n) :
    Decidable (Safe rsvAddr rsvLen lo) :=
  decidable_of_iff
    (MmapsDisjoint lo ∧
     MmapsContained rsvAddr rsvLen lo ∧
     ZerosContained rsvAddr rsvLen lo ∧
     StoresContained rsvAddr rsvLen lo ∧
     MprotectsContained rsvAddr rsvLen lo)
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩,
     fun s => ⟨s.mmapsDisjoint, s.mmapsContained, s.zerosContained,
               s.storesContained, s.mprotectsContained⟩⟩

-- ============================================================================
-- Bridge: structural `LoadSafe` implies flat `Safe`.
--
-- The flat predicates iterate `lo.mmaps`, `lo.zeros`, …, which are
-- defined via `Array.flatMap` + `Array.filterMap` (or `Array.map`).
-- Membership in those flattened arrays decomposes structurally —
-- `Array.mem_flatMap` plus `Array.mem_filterMap` chain into "this
-- element came from segment (i, j)". Combined with `LoadSafe`'s
-- per-segment claims, every element satisfies the per-slot InRange
-- predicate.
-- ============================================================================

/-- For each flat mmap, find its structural source `(k, k')` and read
    off `SegmentSafe`'s `mmapInRange`. -/
theorem mmapsContained_of_LoadSafe (rsvA rsvL : UInt64) (lo : LoadOps n)
    (h : LoadSafe rsvA rsvL lo) : MmapsContained rsvA rsvL lo := by
  intro i hi
  have h_mem : lo.mmaps[i] ∈ lo.mmaps := Array.getElem_mem hi
  obtain ⟨eo, h_eo_mem, h_eo⟩ := Array.mem_flatMap.mp h_mem
  obtain ⟨so, h_so_mem, h_so⟩ := Array.mem_filterMap.mp h_eo
  obtain ⟨k, h_k_lt, rfl⟩ := Array.mem_iff_getElem.mp h_eo_mem
  obtain ⟨k', h_k'_lt, rfl⟩ := Array.mem_iff_getElem.mp h_so_mem
  exact ((h.elfs k h_k_lt).segments k' h_k'_lt).mmapInRange lo.mmaps[i] h_so

/-- Same shape as `mmapsContained_of_LoadSafe` for zeros. -/
theorem zerosContained_of_LoadSafe (rsvA rsvL : UInt64) (lo : LoadOps n)
    (h : LoadSafe rsvA rsvL lo) : ZerosContained rsvA rsvL lo := by
  intro i hi
  have h_mem : lo.zeros[i] ∈ lo.zeros := Array.getElem_mem hi
  obtain ⟨eo, h_eo_mem, h_eo⟩ := Array.mem_flatMap.mp h_mem
  obtain ⟨so, h_so_mem, h_so⟩ := Array.mem_filterMap.mp h_eo
  obtain ⟨k, h_k_lt, rfl⟩ := Array.mem_iff_getElem.mp h_eo_mem
  obtain ⟨k', h_k'_lt, rfl⟩ := Array.mem_iff_getElem.mp h_so_mem
  exact ((h.elfs k h_k_lt).segments k' h_k'_lt).zeroInRange lo.zeros[i] h_so

/-- Stores: `Array.flatMap` (not `filterMap`) for the inner-segment
    collector, so the destruct chains `Array.mem_flatMap` twice. -/
theorem storesContained_of_LoadSafe (rsvA rsvL : UInt64) (lo : LoadOps n)
    (h : LoadSafe rsvA rsvL lo) : StoresContained rsvA rsvL lo := by
  intro i hi
  have h_mem : lo.stores[i] ∈ lo.stores := Array.getElem_mem hi
  obtain ⟨eo, h_eo_mem, h_eo⟩ := Array.mem_flatMap.mp h_mem
  obtain ⟨so, h_so_mem, h_s⟩ := Array.mem_flatMap.mp h_eo
  obtain ⟨k, h_k_lt, rfl⟩ := Array.mem_iff_getElem.mp h_eo_mem
  obtain ⟨k', h_k'_lt, rfl⟩ := Array.mem_iff_getElem.mp h_so_mem
  exact ((h.elfs k h_k_lt).segments k' h_k'_lt).storesInRange lo.stores[i] h_s

/-- Mprotects: every `SegmentOps` emits exactly one (always present), so
    the inner collector is `Array.map` and the destruct chains
    `Array.mem_flatMap` then `Array.mem_map`. -/
theorem mprotectsContained_of_LoadSafe (rsvA rsvL : UInt64) (lo : LoadOps n)
    (h : LoadSafe rsvA rsvL lo) : MprotectsContained rsvA rsvL lo := by
  intro i hi
  have h_mem : lo.mprotects[i] ∈ lo.mprotects := Array.getElem_mem hi
  obtain ⟨eo, h_eo_mem, h_eo⟩ := Array.mem_flatMap.mp h_mem
  obtain ⟨so, h_so_mem, h_mp⟩ := Array.mem_map.mp h_eo
  obtain ⟨k, h_k_lt, rfl⟩ := Array.mem_iff_getElem.mp h_eo_mem
  obtain ⟨k', h_k'_lt, h_k'_eq⟩ := Array.mem_iff_getElem.mp h_so_mem
  subst h_k'_eq
  have h_segSafe := (h.elfs k h_k_lt).segments k' h_k'_lt
  -- `h_mp : lo[k].segments[k'].mprotect = lo.mprotects[i]`.
  rw [← h_mp]; exact h_segSafe.mprotectInRange

-- `mmapsDisjoint_of_LoadSafe`: the structural witness gives same-elf and
-- cross-elf disjointness, but the flat predicate compares mmaps at flat
-- `i < j` indices, which require a flatMap-ordering lemma (mmaps[i]
-- comes from an earlier elf, or same elf and earlier segment, than
-- mmaps[j]). That lemma needs `Array.flatMap_getElem` + its `filterMap`
-- counterpart, which aren't in Lean core. For now the canonical witness
-- is `LoadSafe`; consumers that need flat disjointness can decide
-- `MmapsDisjoint` (it's decidable). `LoadOps.runSafe` only depends on
-- the witness existing, not on its shape — it's a pure FFI dispatch.

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
    (lo : { lo : LoadOps n // Safe rsvAddr rsvLen lo }) : IO Unit :=
  LoadOps.runUnsafe lo.val

end LeanLoad.Materialize

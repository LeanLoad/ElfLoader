/-
PT_LOAD-array well-formedness — gabi-07 mandates plus the de-facto
non-overlap convention. `WellFormed` is a Prop-valued structure
bundling all five invariants; field projections (`wf.sorted`,
`wf.alignCong`, …) give per-conjunct access without auxiliary
theorems. A `Decidable` instance lets `elaborate` check the bundle
at runtime and carry the witness forward into `Elf.wellFormed`.

Spec: gabi 07 (`third_party/gabi/docsrc/elf/07-pheader.rst`) § Program
Loading and § Program Header.

Invariants are stated over `Array Segment` rather than `Array RawPhdr`
so the witness attaches directly to `Elf.segments` — no
`segments.map (·.phdr) = loadable` lemma is needed.

The single-segment definitions (`containsRela`, `Segment` bundle, the
`PF_*` flag bits) live in `Elaborate/Segment.lean`.
-/

import LeanLoad.Elaborate.Segment

namespace LeanLoad.Elaborate

-- ============================================================================
-- gabi-07 invariants on the elaborated PT_LOAD segments. Bound the
-- index in front of the quantifier so each Prop is `Decidable` via
-- `Nat.decidableBAllLT`.
-- ============================================================================

/-- gabi 07 § Program Loading: PT_LOAD entries appear in `p_vaddr` order. -/
def Sorted (segs : Array Segment) : Prop :=
  ∀ i, ∀ _ : i < segs.size, ∀ j, ∀ _ : j < segs.size,
    i < j → segs[i].phdr.p_vaddr ≤ segs[j].phdr.p_vaddr

/-- gabi 07 § Program Header (PT_LOAD): "p_memsz cannot be smaller
    than p_filesz". The `[p_filesz, p_memsz)` tail is BSS. -/
def FileszLeMemsz (segs : Array Segment) : Prop :=
  ∀ i, ∀ _ : i < segs.size, segs[i].phdr.p_filesz ≤ segs[i].phdr.p_memsz

/-- gabi 07 § Program Header: "If p_align is greater than zero, it
    must be a positive integral power of two". `p_align = 0` means
    "no alignment constraint" and is treated as 1 by the loader. -/
def AlignPow2 (segs : Array Segment) : Prop :=
  ∀ i, ∀ _ : i < segs.size,
    segs[i].phdr.p_align = 0 ∨
      (segs[i].phdr.p_align &&& (segs[i].phdr.p_align - 1)) = 0

/-- gabi 07 § Program Header: "p_vaddr should equal p_offset, modulo
    p_align". Specified as SHOULD, not MUST, but the loader's
    `Layout.fileOffsetPaged` relies on it. -/
def AlignCong (segs : Array Segment) : Prop :=
  ∀ i, ∀ _ : i < segs.size,
    segs[i].phdr.p_align = 0 ∨
      segs[i].phdr.p_vaddr % segs[i].phdr.p_align =
        segs[i].phdr.p_offset % segs[i].phdr.p_align

/-- *De facto*, not gabi-mandated: PT_LOAD `[p_vaddr, p_vaddr +
    p_memsz)` ranges are pairwise disjoint. -/
def NonOverlap (segs : Array Segment) : Prop :=
  ∀ i, ∀ _ : i < segs.size, ∀ j, ∀ _ : j < segs.size,
    i < j → segs[i].phdr.p_vaddr + segs[i].phdr.p_memsz ≤ segs[j].phdr.p_vaddr

instance (segs : Array Segment) : Decidable (Sorted segs) := by
  unfold Sorted; infer_instance
instance (segs : Array Segment) : Decidable (FileszLeMemsz segs) := by
  unfold FileszLeMemsz; infer_instance
instance (segs : Array Segment) : Decidable (AlignPow2 segs) := by
  unfold AlignPow2; infer_instance
instance (segs : Array Segment) : Decidable (AlignCong segs) := by
  unfold AlignCong; infer_instance
instance (segs : Array Segment) : Decidable (NonOverlap segs) := by
  unfold NonOverlap; infer_instance

-- ============================================================================
-- The bundle. A Prop-valued structure: one field per gabi-07 mandate,
-- so `wf.sorted`, `wf.alignCong`, … are auto-generated projections.
-- ============================================================================

/-- The PT_LOAD segments satisfy all gabi-07 mandates plus the
    de-facto non-overlap convention. Built by `elaborate` and carried
    on `Elf.wellFormed` so downstream consumers don't re-check. -/
structure WellFormed (segs : Array Segment) : Prop where
  sorted        : Sorted segs
  fileszLeMemsz : FileszLeMemsz segs
  alignPow2     : AlignPow2 segs
  alignCong     : AlignCong segs
  nonOverlap    : NonOverlap segs

instance (segs : Array Segment) : Decidable (WellFormed segs) :=
  decidable_of_iff
    (Sorted segs ∧ FileszLeMemsz segs ∧ AlignPow2 segs ∧
     AlignCong segs ∧ NonOverlap segs)
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩,
     fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

theorem WellFormed_nil : WellFormed (#[] : Array Segment) := by decide

-- ============================================================================
-- PT_LOAD filter — the input shape `elaborate` feeds into segment
-- construction. Lives here because it's the bridge between raw phdrs
-- and the well-formedness check.
-- ============================================================================

open LeanLoad.Parse (RawPhdr)

/-- Extract loadable phdrs from the raw phdr table. Each element is
    a phdr with `p_type = PT_LOAD` (the proof is left implicit; the
    bundle `Elaborate.Segment` carries it explicitly when needed). -/
def fromPhdrs (phdrs : Array RawPhdr) : Array RawPhdr :=
  phdrs.filter (·.p_type == Parse.PT_LOAD)

-- ============================================================================
-- Examples — read each input list as a sentence describing the case.
-- ============================================================================

section Example
open LeanLoad.Parse (PT_LOAD RawRela)

private def mkSeg (vaddr memsz filesz align offset : UInt64) : Segment :=
  { phdr :=
      { (default : RawPhdr) with
          p_type := PT_LOAD,
          p_vaddr := vaddr, p_memsz := memsz, p_filesz := filesz,
          p_align := align, p_offset := offset }
    isLoad := rfl
    rela := #[]
    jmprel := #[] }

private def textSeg : Segment :=
  mkSeg (vaddr := 0x1000) (memsz := 0x1000) (filesz := 0x800)
        (align := 0x1000) (offset := 0x1000)

private def dataSeg : Segment :=
  mkSeg (vaddr := 0x3000) (memsz := 0x500) (filesz := 0x500)
        (align := 0x1000) (offset := 0x2000)

private def overlappingSeg : Segment :=
  mkSeg (vaddr := 0x1800) (memsz := 0x500) (filesz := 0x500)
        (align := 0x1000) (offset := 0x1800)

private def filesizeTooBig : Segment :=
  mkSeg (vaddr := 0x1000) (memsz := 0x100) (filesz := 0x200)
        (align := 0x1000) (offset := 0x1000)

private def badAlign : Segment :=
  mkSeg (vaddr := 0x1000) (memsz := 0x100) (filesz := 0x100)
        (align := 3) (offset := 0x1000)

private def badCongruence : Segment :=
  mkSeg (vaddr := 0x1000) (memsz := 0x100) (filesz := 0x100)
        (align := 0x1000) (offset := 0x1004)

#guard decide (WellFormed #[textSeg, dataSeg]) = true
#guard decide (WellFormed (#[] : Array Segment)) = true
#guard decide (WellFormed #[dataSeg, textSeg]) = false
#guard decide (WellFormed #[textSeg, overlappingSeg]) = false
#guard decide (WellFormed #[filesizeTooBig]) = false
#guard decide (WellFormed #[badAlign]) = false
#guard decide (WellFormed #[badCongruence]) = false
end Example

end LeanLoad.Elaborate

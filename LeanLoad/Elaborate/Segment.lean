/-
Loadable segments — the validated form.

A `Parse.RawPhdr` becomes an `Elaborate.Segment` only after we
verify `p_type = PT_LOAD` and locate the relocations targeting it.
This file owns:

  - Per-segment containment predicate (`containsRela`).
  - Decidable parse-time well-formedness check (`WellFormedB`) plus
    the propositional reading (`WellFormed`) and the Prop-level
    statements of gabi-07 mandates.
  - `fromPhdrs` — the PT_LOAD filter.
  - `Elaborate.Segment` — bundle `(phdr, rela, jmprel)` carrying the
    `isLoad : phdr.p_type = PT_LOAD` proof.
  - Named accessors that derive each gabi-07 invariant from a
    `WellFormed` witness.

Loader-level views (`vaddr`, `length`, `prot`, `endAddr`, …) — which
page-align addresses for `mmap(2)` and translate `PF_*` to POSIX
`PROT_*` — live in `LeanLoad.Layout`. Those are decisions the loader
makes, not properties the spec dictates.
-/

import LeanLoad.Parse.Structs

-- ============================================================================
-- Per-rela containment predicate. Defined in `Parse.RawPhdr`'s
-- own namespace so dot notation (`phdr.containsRela r`) resolves;
-- the predicate is morally an Elaborate concept (semantic check on
-- raw bytes), but Lean's dot resolution lives by the type's home
-- namespace.
-- ============================================================================

namespace LeanLoad.Parse.RawPhdr

open LeanLoad.Parse (RawPhdr RawRela)

/-- The phdr's memory range fully contains the rela's 8-byte write
    window. Conservatively reserves 8 bytes (the maximum dynamic
    relocation width); 4-byte relocs trivially fit too. The witness
    `phdr.containsRela r` is the bound carried inside
    `Elaborate.Segment`'s rela arrays — established by `elaborate` at
    the parse boundary, consumed downstream for region-bounds-by-
    construction. -/
def containsRela (p : RawPhdr) (r : RawRela) : Prop :=
  p.p_vaddr.toNat ≤ r.r_offset.toNat ∧
  r.r_offset.toNat + 8 ≤ p.p_vaddr.toNat + p.p_memsz.toNat

instance (p : RawPhdr) (r : RawRela) : Decidable (p.containsRela r) := by
  unfold containsRela; infer_instance

end LeanLoad.Parse.RawPhdr

namespace LeanLoad.Elaborate

open LeanLoad.Parse (RawPhdr RawRela)

-- p_flags (gabi 07 Table: Segment Flag Bits)
def PF_X : UInt32 := 0x1
def PF_W : UInt32 := 0x2
def PF_R : UInt32 := 0x4

-- ============================================================================
-- gabi-07 Prop-level invariants on PT_LOAD-filtered phdrs.
-- ============================================================================

/-- gabi 07 § Program Loading: PT_LOAD entries appear in `p_vaddr` order. -/
def Sorted (segs : Array RawPhdr) : Prop :=
  ∀ i j (_ : i < segs.size) (_ : j < segs.size),
    i < j → segs[i].p_vaddr ≤ segs[j].p_vaddr

/-- gabi 07 § Program Header (PT_LOAD): "p_memsz cannot be smaller
    than p_filesz". The `[p_filesz, p_memsz)` tail is BSS. -/
def FileszLeMemsz (segs : Array RawPhdr) : Prop :=
  ∀ i (_ : i < segs.size), segs[i].p_filesz ≤ segs[i].p_memsz

/-- gabi 07 § Program Header: "If p_align is greater than zero, it
    must be a positive integral power of two". `p_align = 0` means
    "no alignment constraint" and is treated as 1 by the loader. -/
def AlignPow2 (segs : Array RawPhdr) : Prop :=
  ∀ i (_ : i < segs.size),
    segs[i].p_align = 0 ∨
    (segs[i].p_align &&& (segs[i].p_align - 1)) = 0

/-- gabi 07 § Program Header: "p_vaddr should equal p_offset, modulo
    p_align". Specified as SHOULD, not MUST, but the loader's
    `Layout.fileOffsetPaged` relies on it. -/
def AlignCong (segs : Array RawPhdr) : Prop :=
  ∀ i (_ : i < segs.size),
    segs[i].p_align = 0 ∨
    segs[i].p_vaddr % segs[i].p_align =
      segs[i].p_offset % segs[i].p_align

/-- *De facto*, not gabi-mandated: PT_LOAD `[p_vaddr, p_vaddr +
    p_memsz)` ranges are pairwise disjoint. -/
def NonOverlap (segs : Array RawPhdr) : Prop :=
  ∀ i j (_ : i < segs.size) (_ : j < segs.size),
    i < j →
    segs[i].p_vaddr + segs[i].p_memsz ≤ segs[j].p_vaddr

-- ============================================================================
-- Decidable well-formedness — runs in `elaborate`, rejects malformed
-- ELFs at the parse boundary.
-- ============================================================================

/-- Decidable parse-time well-formedness check on PT_LOAD-filtered
    phdrs. Bundles four gabi-07 mandates plus one de-facto convention. -/
def WellFormedB (segs : Array RawPhdr) : Bool :=
  let pair (p : RawPhdr → RawPhdr → Bool) : Bool :=
    (List.range segs.size).all fun i =>
      (List.range segs.size).all fun j =>
        !decide (i < j) ||
          (match segs[i]?, segs[j]? with
           | some s, some s' => p s s'
           | _, _ => true)
  let perEntry (p : RawPhdr → Bool) : Bool :=
    (List.range segs.size).all fun i =>
      match segs[i]? with
      | some s => p s
      | none   => true
  pair (fun s s' => decide (s.p_vaddr ≤ s'.p_vaddr)) &&
  perEntry (fun s => decide (s.p_filesz ≤ s.p_memsz)) &&
  perEntry (fun s =>
    let a := s.p_align
    decide (a = 0) || decide ((a &&& (a - 1)) = 0)) &&
  perEntry (fun s =>
    let a := s.p_align
    decide (a = 0) ||
    decide (s.p_vaddr % a = s.p_offset % a)) &&
  pair (fun s s' =>
    decide (s.p_vaddr + s.p_memsz ≤ s'.p_vaddr))

/-- Propositional reading of `WellFormedB`. -/
abbrev WellFormed (segs : Array RawPhdr) : Prop := WellFormedB segs = true

theorem WellFormed_nil : WellFormed (#[] : Array RawPhdr) := by decide

-- ============================================================================
-- PT_LOAD filter.
-- ============================================================================

/-- Extract loadable phdrs from the raw phdr table. Each element is
    a phdr with `p_type = PT_LOAD` (the proof is left implicit; the
    bundle `Elaborate.Segment` carries it explicitly when needed). -/
def fromPhdrs (phdrs : Array RawPhdr) : Array RawPhdr :=
  phdrs.filter (·.p_type == Parse.PT_LOAD)

-- ============================================================================
-- Examples — read each input list as a sentence describing the case.
-- ============================================================================

section Example
open LeanLoad.Parse (PT_LOAD)

private def mkSeg (vaddr memsz filesz align offset : UInt64) : RawPhdr :=
  { (default : RawPhdr) with
      p_type := PT_LOAD,
      p_vaddr := vaddr, p_memsz := memsz, p_filesz := filesz,
      p_align := align, p_offset := offset,
      p_flags := PF_R ||| PF_W }

private def textSeg : RawPhdr :=
  mkSeg (vaddr := 0x1000) (memsz := 0x1000) (filesz := 0x800)
        (align := 0x1000) (offset := 0x1000)

private def dataSeg : RawPhdr :=
  mkSeg (vaddr := 0x3000) (memsz := 0x500) (filesz := 0x500)
        (align := 0x1000) (offset := 0x2000)

private def overlappingSeg : RawPhdr :=
  mkSeg (vaddr := 0x1800) (memsz := 0x500) (filesz := 0x500)
        (align := 0x1000) (offset := 0x1800)

private def filesizeTooBig : RawPhdr :=
  mkSeg (vaddr := 0x1000) (memsz := 0x100) (filesz := 0x200)
        (align := 0x1000) (offset := 0x1000)

private def badAlign : RawPhdr :=
  mkSeg (vaddr := 0x1000) (memsz := 0x100) (filesz := 0x100)
        (align := 3) (offset := 0x1000)

private def badCongruence : RawPhdr :=
  mkSeg (vaddr := 0x1000) (memsz := 0x100) (filesz := 0x100)
        (align := 0x1000) (offset := 0x1004)

#guard WellFormedB #[textSeg, dataSeg] = true
#guard WellFormedB (#[] : Array RawPhdr) = true
#guard WellFormedB #[dataSeg, textSeg] = false
#guard WellFormedB #[textSeg, overlappingSeg] = false
#guard WellFormedB #[filesizeTooBig] = false
#guard WellFormedB #[badAlign] = false
#guard WellFormedB #[badCongruence] = false
end Example

-- ============================================================================
-- The validated per-segment bundle: a PT_LOAD phdr + its located
-- dynamic relocations. Built by `Elaborate.elaborate`.
-- ============================================================================

/-- A loadable segment plus its located relocations. -/
structure Segment where
  /-- The underlying phdr. The `isLoad` field below is its PT_LOAD
      witness. -/
  phdr   : RawPhdr
  isLoad : phdr.p_type = Parse.PT_LOAD
  /-- General `Rela` relocations (from `DT_RELA`) that target this
      segment. The subtype witness binds each rela's write window
      inside `phdr`'s memory range. -/
  rela   : Array { r : RawRela // phdr.containsRela r }
  /-- PLT relocations (from `DT_JMPREL`) that target this segment. -/
  jmprel : Array { r : RawRela // phdr.containsRela r }

end LeanLoad.Elaborate

-- ============================================================================
-- Named accessors: derive each gabi-07 invariant from a `WellFormed`
-- witness. Live outside the `LeanLoad.Elaborate` namespace because
-- `Segment` there means the bundle; here we work with raw `phdrs`.
-- ============================================================================

namespace LeanLoad.Elaborate.WellFormed

private abbrev Phdr := LeanLoad.Parse.RawPhdr

/-- Helper: a successful pairwise scan inside `WellFormedB` yields
    the per-pair predicate at every `i < j`. -/
private theorem of_pair {segs : Array Phdr} {p : Phdr → Phdr → Bool}
    (hp : ((List.range segs.size).all fun i =>
      (List.range segs.size).all fun j =>
        !decide (i < j) ||
          match segs[i]?, segs[j]? with
          | some s, some s' => p s s'
          | _, _ => true) = true)
    (i j : Nat) (hi : i < segs.size) (hj : j < segs.size) (hlt : i < j) :
    p segs[i] segs[j] = true := by
  rw [List.all_eq_true] at hp
  have hpi := hp i (List.mem_range.mpr hi)
  rw [List.all_eq_true] at hpi
  have hpij := hpi j (List.mem_range.mpr hj)
  rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hj] at hpij
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
             decide_eq_false_iff_not] at hpij
  rcases hpij with hnlt | hp'
  · exact absurd hlt hnlt
  · exact hp'

/-- Helper: a successful per-entry scan inside `WellFormedB` yields
    the predicate at every index. -/
private theorem of_perEntry {segs : Array Phdr} {p : Phdr → Bool}
    (hp : ((List.range segs.size).all fun i =>
      match segs[i]? with
      | some s => p s
      | none   => true) = true)
    (i : Nat) (hi : i < segs.size) : p segs[i] = true := by
  rw [List.all_eq_true] at hp
  have hpi := hp i (List.mem_range.mpr hi)
  rw [Array.getElem?_eq_getElem hi] at hpi
  exact hpi

/-- Destructure the conjunctive `WellFormedB` body into its five
    component scans. -/
private theorem unpack {segs : Array Phdr}
    (h : LeanLoad.Elaborate.WellFormed segs) :
    ((List.range segs.size).all fun i =>
      (List.range segs.size).all fun j =>
        !decide (i < j) ||
          match segs[i]?, segs[j]? with
          | some s, some s' => decide (s.p_vaddr ≤ s'.p_vaddr)
          | _, _ => true) = true ∧
    ((List.range segs.size).all fun i =>
      match segs[i]? with
      | some s => decide (s.p_filesz ≤ s.p_memsz)
      | none   => true) = true ∧
    ((List.range segs.size).all fun i =>
      match segs[i]? with
      | some s =>
        let a := s.p_align
        decide (a = 0) || decide ((a &&& (a - 1)) = 0)
      | none   => true) = true ∧
    ((List.range segs.size).all fun i =>
      match segs[i]? with
      | some s =>
        let a := s.p_align
        decide (a = 0) || decide (s.p_vaddr % a = s.p_offset % a)
      | none   => true) = true ∧
    ((List.range segs.size).all fun i =>
      (List.range segs.size).all fun j =>
        !decide (i < j) ||
          match segs[i]?, segs[j]? with
          | some s, some s' => decide (s.p_vaddr + s.p_memsz ≤ s'.p_vaddr)
          | _, _ => true) = true := by
  unfold LeanLoad.Elaborate.WellFormed LeanLoad.Elaborate.WellFormedB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem sorted {segs : Array Phdr}
    (h : LeanLoad.Elaborate.WellFormed segs) :
    LeanLoad.Elaborate.Sorted segs := by
  intro i j hi hj hlt
  exact decide_eq_true_eq.mp (of_pair (unpack h).1 i j hi hj hlt)

theorem fileszLeMemsz {segs : Array Phdr}
    (h : LeanLoad.Elaborate.WellFormed segs) :
    LeanLoad.Elaborate.FileszLeMemsz segs := by
  intro i hi
  exact decide_eq_true_eq.mp (of_perEntry (unpack h).2.1 i hi)

theorem alignPow2 {segs : Array Phdr}
    (h : LeanLoad.Elaborate.WellFormed segs) :
    LeanLoad.Elaborate.AlignPow2 segs := by
  intro i hi
  have := of_perEntry (unpack h).2.2.1 i hi
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  exact this

theorem alignCong {segs : Array Phdr}
    (h : LeanLoad.Elaborate.WellFormed segs) :
    LeanLoad.Elaborate.AlignCong segs := by
  intro i hi
  have := of_perEntry (unpack h).2.2.2.1 i hi
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  exact this

theorem nonOverlap {segs : Array Phdr}
    (h : LeanLoad.Elaborate.WellFormed segs) :
    LeanLoad.Elaborate.NonOverlap segs := by
  intro i j hi hj hlt
  exact decide_eq_true_eq.mp (of_pair (unpack h).2.2.2.2 i j hi hj hlt)

end LeanLoad.Elaborate.WellFormed

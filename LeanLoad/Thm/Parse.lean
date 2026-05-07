/-
Parser-side theorems.

Named accessors that derive each gabi-07 / de-facto invariant from a
parse-time `Parse.Segment.WellFormed` witness. The Bool decision
procedure is in `Parse/Segment.lean`; the Prop-level statements
(`Spec.Program.{Sorted, FileszLeMemsz, AlignPow2, AlignCong,
NonOverlap}`) live in `Spec/Program.lean`. This file bridges: given
`WellFormedB segs = true`, produce the corresponding Spec-level
Prop. Production code (`Parse.File.parse`, `LoadedObject.elf_wf`)
treats the witness as opaque; only proofs that need to destructure
individual clauses use these accessors.

The companion theorem `vaToOffset_correct` was retired: the witness
is now in `Parse.File.vaToOffset`'s return type as a subtype.
-/

import LeanLoad.Spec.Program
import LeanLoad.Parse.File

namespace LeanLoad.Thm

open LeanLoad.Spec
open LeanLoad.Spec.Program (Segment)
open LeanLoad.Parse.Segment

-- ============================================================================
-- Named accessors on `Parse.Segment.WellFormed`.
--
-- `WellFormed segs := WellFormedB segs = true` is the propositional
-- reading of the Bool decision procedure (in `Parse/Segment.lean`).
-- The Prop-level statements of each clause live in `Spec.Program`.
-- The accessors below bridge: given a `WellFormed` witness, produce
-- the corresponding `Spec.Program.*` Prop.
-- ============================================================================

namespace WellFormed

/-- Helper: a successful pairwise scan inside `WellFormedB` yields
    the per-pair predicate at every `i < j`. -/
private theorem of_pair {segs : Array Segment} {p : Segment → Segment → Bool}
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
private theorem of_perEntry {segs : Array Segment} {p : Segment → Bool}
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
    component scans. Used by every accessor below. -/
private theorem unpack {segs : Array Segment} (h : WellFormed segs) :
    ((List.range segs.size).all fun i =>
      (List.range segs.size).all fun j =>
        !decide (i < j) ||
          match segs[i]?, segs[j]? with
          | some s, some s' => decide (s.phdr.p_vaddr ≤ s'.phdr.p_vaddr)
          | _, _ => true) = true ∧
    ((List.range segs.size).all fun i =>
      match segs[i]? with
      | some s => decide (s.phdr.p_filesz ≤ s.phdr.p_memsz)
      | none   => true) = true ∧
    ((List.range segs.size).all fun i =>
      match segs[i]? with
      | some s =>
        let a := s.phdr.p_align
        decide (a = 0) || decide ((a &&& (a - 1)) = 0)
      | none   => true) = true ∧
    ((List.range segs.size).all fun i =>
      match segs[i]? with
      | some s =>
        let a := s.phdr.p_align
        decide (a = 0) || decide (s.phdr.p_vaddr % a = s.phdr.p_offset % a)
      | none   => true) = true ∧
    ((List.range segs.size).all fun i =>
      (List.range segs.size).all fun j =>
        !decide (i < j) ||
          match segs[i]?, segs[j]? with
          | some s, some s' => decide (s.phdr.p_vaddr + s.phdr.p_memsz ≤ s'.phdr.p_vaddr)
          | _, _ => true) = true := by
  unfold WellFormed WellFormedB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- A `WellFormed` witness yields `Spec.Program.Sorted`. -/
theorem sorted {segs : Array Segment} (h : WellFormed segs) :
    Spec.Program.Sorted segs := by
  intro i j hi hj hlt
  exact decide_eq_true_eq.mp (of_pair (unpack h).1 i j hi hj hlt)

/-- A `WellFormed` witness yields `Spec.Program.FileszLeMemsz`. -/
theorem fileszLeMemsz {segs : Array Segment} (h : WellFormed segs) :
    Spec.Program.FileszLeMemsz segs := by
  intro i hi
  exact decide_eq_true_eq.mp (of_perEntry (unpack h).2.1 i hi)

/-- A `WellFormed` witness yields `Spec.Program.AlignPow2`. -/
theorem alignPow2 {segs : Array Segment} (h : WellFormed segs) :
    Spec.Program.AlignPow2 segs := by
  intro i hi
  have := of_perEntry (unpack h).2.2.1 i hi
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  exact this

/-- A `WellFormed` witness yields `Spec.Program.AlignCong`. -/
theorem alignCong {segs : Array Segment} (h : WellFormed segs) :
    Spec.Program.AlignCong segs := by
  intro i hi
  have := of_perEntry (unpack h).2.2.2.1 i hi
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  exact this

/-- A `WellFormed` witness yields `Spec.Program.NonOverlap`. -/
theorem nonOverlap {segs : Array Segment} (h : WellFormed segs) :
    Spec.Program.NonOverlap segs := by
  intro i j hi hj hlt
  exact decide_eq_true_eq.mp (of_pair (unpack h).2.2.2.2 i j hi hj hlt)

end WellFormed

end LeanLoad.Thm

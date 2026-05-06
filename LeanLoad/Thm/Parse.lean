/-
Parser-side theorems.

- `Parse.File.vaToOffset` returns the offset of the file byte that
  should appear at the requested virtual address.
- Named accessors for the parse-time well-formedness witness
  (`Parse.Segment.WellFormed`, defined as `WellFormedB segs = true`).
  These let proof-side code destructure individual clauses (sorted,
  nonOverlap, …) when needed; the production path (`Parse.File.parse`,
  `LoadedObject.elf_wf`) treats the witness as opaque.
-/

import LeanLoad.Spec.Program
import LeanLoad.Parse.File

namespace LeanLoad.Thm

open LeanLoad.Spec
open LeanLoad.Parse.Segment

/-- If `vaToOffset` returns `some off`, there is a witness `PT_LOAD`
    segment in `phdrs` whose virtual range covers `va` and `off` is
    the corresponding file offset. -/
theorem vaToOffset_correct
    (phdrs : Array Program.Header64) (va : UInt64) (off : Nat) :
    Parse.File.vaToOffset phdrs va = some off →
    ∃ ph ∈ phdrs,
      ph.p_type = Program.PT_LOAD ∧
      ph.p_vaddr ≤ va ∧
      va < ph.p_vaddr + ph.p_memsz ∧
      off = (va - ph.p_vaddr).toNat + ph.p_offset.toNat := by
  intro h
  unfold Parse.File.vaToOffset at h
  obtain ⟨ph, hmem, hf⟩ := Array.exists_of_findSome?_eq_some h
  refine ⟨ph, hmem, ?_⟩
  split at hf
  · rename_i hcond
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
    refine ⟨hcond.1.1, hcond.1.2, hcond.2, ?_⟩
    injection hf with hf; exact hf.symm
  · contradiction

-- ============================================================================
-- Named accessors on `Parse.Segment.WellFormed`.
--
-- `WellFormed segs := WellFormedB segs = true` is the propositional
-- reading of the Bool decision procedure, with no separate Prop
-- structure. The accessors below extract individual clauses from a
-- witness — they decode the conjunctive Bool by hand. Same layout as
-- the structure-style fields would have given, just lazy: only the
-- clauses callers actually consume need accessor lemmas.
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

/-- gabi 07 § Program Loading: PT_LOAD entries appear in `p_vaddr` order. -/
theorem sorted {segs : Array Segment} (h : WellFormed segs) :
    ∀ i j (_ : i < segs.size) (_ : j < segs.size),
      i < j → segs[i].phdr.p_vaddr ≤ segs[j].phdr.p_vaddr := by
  intro i j hi hj hlt
  exact decide_eq_true_eq.mp (of_pair (unpack h).1 i j hi hj hlt)

/-- gabi 07 § Program Header (PT_LOAD): `p_filesz ≤ p_memsz`. -/
theorem fileszLeMemsz {segs : Array Segment} (h : WellFormed segs) :
    ∀ i (_ : i < segs.size),
      segs[i].phdr.p_filesz ≤ segs[i].phdr.p_memsz := by
  intro i hi
  exact decide_eq_true_eq.mp (of_perEntry (unpack h).2.1 i hi)

/-- gabi 07 § Program Header: `p_align` is 0 or a power of two. -/
theorem alignPow2 {segs : Array Segment} (h : WellFormed segs) :
    ∀ i (_ : i < segs.size),
      segs[i].phdr.p_align = 0 ∨
      (segs[i].phdr.p_align &&& (segs[i].phdr.p_align - 1)) = 0 := by
  intro i hi
  have := of_perEntry (unpack h).2.2.1 i hi
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  exact this

/-- gabi 07 § Program Header: `p_vaddr ≡ p_offset (mod p_align)`. -/
theorem alignCong {segs : Array Segment} (h : WellFormed segs) :
    ∀ i (_ : i < segs.size),
      segs[i].phdr.p_align = 0 ∨
      segs[i].phdr.p_vaddr % segs[i].phdr.p_align =
        segs[i].phdr.p_offset % segs[i].phdr.p_align := by
  intro i hi
  have := of_perEntry (unpack h).2.2.2.1 i hi
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  exact this

/-- *De facto* (not gabi-mandated): PT_LOAD `[p_vaddr, p_vaddr + p_memsz)`
    ranges are pairwise disjoint. -/
theorem nonOverlap {segs : Array Segment} (h : WellFormed segs) :
    ∀ i j (_ : i < segs.size) (_ : j < segs.size),
      i < j →
      segs[i].phdr.p_vaddr + segs[i].phdr.p_memsz ≤ segs[j].phdr.p_vaddr := by
  intro i j hi hj hlt
  exact decide_eq_true_eq.mp (of_pair (unpack h).2.2.2.2 i j hi hj hlt)

end WellFormed

end LeanLoad.Thm

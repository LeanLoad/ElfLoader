/-
Parser-side theorems.

`Parse.File.vaToOffset` returns the offset of the file byte that
should appear at the requested virtual address.
-/

import LeanLoad.Spec.Program
import LeanLoad.Parse.File

namespace LeanLoad.Thm

open LeanLoad.Spec

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

end LeanLoad.Thm

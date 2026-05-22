  /-
Properties over checked PT_LOAD segment arrays.

Spec: gabi 07 (`third_party/gabi/docsrc/elf/07-pheader.rst`) § Program
Loading.

`Segment.Array` owns the checked segment-array wrapper and its array-level
ordering/disjointness invariants. This file owns the remaining checked-ELF
coverage predicates: phdr-table coverage and init/fini-array target coverage.
-/

import LeanLoad.Parse.ImageView.Segment.Array

namespace LeanLoad.Parse

-- ============================================================================
-- ProgramHeader mapping — when the runtime emits `AT_PHDR`, a PT_LOAD segment must
-- file-back the program-header table. The value is computed by translating
-- `e_phoff` through the covering segment, not by assuming `p_vaddr = p_offset`.
-- ============================================================================

/-- The PT_LOAD segment `s` file-backs the program-header table at file offset
    `phoff` of byte length `nbytes`. -/
def coversPhdrs (s : Segment) (phoff : FileOff) (nbytes : Nat) : Prop :=
  s.offset.toNat ≤ phoff.toNat ∧
  phoff.toNat + nbytes ≤ s.offset.toNat + s.filesz.toNat

/-- Checked phdr-table mapping for `AT_PHDR`. This carries the segment index
    needed to translate the table's file offset into its loaded ELF address. -/
inductive PhdrMap (segments : Segments) (phoff : FileOff) (nbytes : Nat) where
  | empty (isEmpty : nbytes = 0)
  | mapped (index : Fin segments.items.size)
      (covers : coversPhdrs segments.items[index] phoff nbytes)
  deriving Repr

namespace PhdrMap

/-- Virtual address of the program-header table in the loaded image, relative to
    the object's base. For `phnum = 0`, `AT_PHDR` is unused and this returns 0. -/
def eaddr {segments : Segments} {phoff : FileOff} {nbytes : Nat}
    (m : PhdrMap segments phoff nbytes) : Eaddr :=
  match m with
  | .empty _ => 0
  | .mapped index _ => segments.items[index].eaddrOfFileOff phoff

/-- Build a checked phdr-table mapping by searching the checked PT_LOAD array. -/
def ofSegments (segments : Segments) (phoff : FileOff) (nbytes : Nat) :
    Except String (PhdrMap segments phoff nbytes) := Id.run do
  if h_empty : nbytes = 0 then
    return .ok (.empty h_empty)
  for h : i in [:segments.items.size] do
    let index : Fin segments.items.size := ⟨i, h.upper⟩
    let decCovers : Decidable (coversPhdrs segments.items[index] phoff nbytes) := by
      unfold coversPhdrs
      infer_instance
    match decCovers with
    | .isTrue h_covers => return .ok (.mapped index h_covers)
    | .isFalse _ => pure ()
  return .error s!"phdr table at file offset \
    0x{phoff.toNat} (size {nbytes}) is not file-backed by any PT_LOAD; \
    AT_PHDR cannot be computed"

end PhdrMap

-- ============================================================================
-- Ctor / dtor address coverage — every non-zero entry in
-- `DT_INIT_ARRAY` / `DT_FINI_ARRAY` is a callable function. For ET_DYN
-- (the only kind LeanLoad supports) the entry is a base-relative
-- ELF address; it must live inside an executable PT_LOAD or
-- calling it segfaults at runtime. Validated during parse so a
-- corrupt binary fails loud during parse.
-- ============================================================================

/-- A function pointer (relative eaddr) is either zero (skip — gabi
    leaves zero entries unspecified, but glibc/musl treat them as
    no-ops) or lives inside an executable PT_LOAD's
    `[eaddr, eaddr + memsz)`. -/
def callTargetInExecSeg (segments : Segments) (entry : Eaddr) : Prop :=
  entry.val = 0 ∨ Segments.ExecAddr segments entry

end LeanLoad.Parse

  /-
Properties over checked PT_LOAD segment arrays.

Spec: gabi 07 (`third_party/gabi/docsrc/elf/07-pheader.rst`) § Program
Loading.

`Segment.Array` owns the checked segment-array wrapper and its array-level
ordering/disjointness invariants. This file owns the remaining checked-ELF
coverage predicates: phdr-table coverage and init/fini-array target coverage.
-/

import LeanLoad.Parse.Segment.Array

namespace LeanLoad.Parse

-- ============================================================================
-- Phdr coverage — a PT_LOAD segment maps the program-header table to
-- the loaded image at virtual address `phoff`. Requires `vaddr =
-- offset` for the covering segment so `mainBase + phoff` equals the
-- runtime `AT_PHDR` without an offset→vaddr translation. By gabi-07
-- convention the first PT_LOAD has both at 0 (or the same aligned
-- base) and contains the ELF header + phdr table.
-- ============================================================================

/-- The PT_LOAD segment `s` file-backs the program-header table at file offset
    `phoff` of byte length `nbytes`, AND its `vaddr` equals its `offset` (so
    `runtime_addr = mainBase + phoff` is consistent with the kernel's
    `AT_PHDR`). -/
def coversPhdrs (s : Segment) (phoff : FileOff) (nbytes : Nat) : Prop :=
  s.vaddr.val = s.offset.val ∧
  s.offset.toNat ≤ phoff.toNat ∧
  phoff.toNat + nbytes ≤ s.offset.toNat + s.filesz.toNat

/-- Some PT_LOAD segment covers the phdr table (per `coversPhdrs`),
    or there's no phdr table to cover (`nbytes = 0`, degenerate Elf
    with `phnum = 0` — `AT_PHDR` is unused in that case). Bounded
    `∃` so it's decidable via `Nat.decidableBExLT`. -/
def PhdrCovered (segs : Array Segment) (phoff : FileOff) (nbytes : Nat) : Prop :=
  nbytes = 0 ∨ ∃ i, ∃ _ : i < segs.size, coversPhdrs segs[i] phoff nbytes

-- ============================================================================
-- Ctor / dtor address coverage — every non-zero entry in
-- `DT_INIT_ARRAY` / `DT_FINI_ARRAY` is a callable function. For ET_DYN
-- (the only kind LeanLoad supports) the entry is a base-relative
-- virtual address; it must live inside an executable PT_LOAD or
-- calling it segfaults at runtime. Validated during parse so a
-- corrupt binary fails loud during parse.
-- ============================================================================

/-- A function pointer (relative vaddr) is either zero (skip — gabi
    leaves zero entries unspecified, but glibc/musl treat them as
    no-ops) or lives inside an executable PT_LOAD's
    `[vaddr, vaddr + memsz)`. -/
def callTargetInExecSeg (segments : Segments) (entry : Vaddr) : Prop :=
  entry.val = 0 ∨ Segments.ExecAddr segments entry

end LeanLoad.Parse

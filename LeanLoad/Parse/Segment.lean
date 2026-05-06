/-
Typed projection of `PT_LOAD` program headers — *parse-level only*.

A `Segment` is a `Spec.Program.Header64` carrying a proof that
`p_type = PT_LOAD`. Trivial accessors over raw header fields
(`fileOff`, `fileLen`) live here because they're zero-computation
projections.

**Loader-level views** (`vaddr`, `length`, `prot`, `endAddr`, …) —
which page-align addresses for `mmap(2)` and translate `PF_*` to
POSIX `PROT_*` — live in `LeanLoad.Layout`. Those are decisions the
loader makes, not properties the spec dictates.

Spec: gabi 07 § Program Header.
-/

import LeanLoad.Spec.Program
import LeanLoad.Parse.File

namespace LeanLoad.Parse.Segment

open LeanLoad
open LeanLoad.Spec

/-- A loadable segment: a `Header64` whose `p_type = PT_LOAD`. The
    `isLoad` field defaults via `decide` for direct construction with
    a concrete phdr; the smart constructor `fromPhdr?` filters
    arbitrary phdrs by type. -/
structure Segment where
  phdr   : Program.Header64
  isLoad : phdr.p_type = Program.PT_LOAD := by decide
  deriving Repr

namespace Segment

/-- Lift a `Header64` into a `Segment` if it is `PT_LOAD`. -/
def fromPhdr? (ph : Program.Header64) : Option Segment :=
  if h : ph.p_type = Program.PT_LOAD then some ⟨ph, h⟩ else none

/-- File offset to start copying bytes from. -/
def fileOff (s : Segment) : UInt64 := s.phdr.p_offset

/-- Number of bytes to copy (≤ memory length; remainder is BSS). -/
def fileLen (s : Segment) : UInt64 := s.phdr.p_filesz

end Segment

/-- Extract the loadable segments from a parsed ELF. Filters
    `phdrs` to `PT_LOAD` entries and wraps each in `Segment`. -/
def segmentsOf (elf : Parse.File.ParsedElf) : Array Segment :=
  elf.phdrs.filterMap Segment.fromPhdr?

-- ============================================================================
-- Well-formedness check (parse-level: raw `p_vaddr` + `p_memsz`)
-- ============================================================================

/-- Bool-decidable check for "PT_LOAD segments are sorted by `p_vaddr`
    with non-overlapping `[p_vaddr, p_vaddr + p_memsz)` ranges". gabi
    07 mandates the sort; non-overlap is de facto (every linker
    produces it; `Map.lean`'s `MAP_FIXED` mmap requires it for
    correctness). The check is at parse level — uses only raw header
    fields, no loader-level page alignment. The O(n²) pairwise scan
    is fine: real ELFs have <10 PT_LOAD entries. -/
def wellFormed (elf : Parse.File.ParsedElf) : Bool :=
  let segs := segmentsOf elf
  (List.range segs.size).all fun i =>
    (List.range segs.size).all fun j =>
      decide (i ≥ j) ||
        (match segs[i]?, segs[j]? with
         | some s, some s' => decide (s.phdr.p_vaddr + s.phdr.p_memsz ≤ s'.phdr.p_vaddr)
         | _, _ => true)

end LeanLoad.Parse.Segment

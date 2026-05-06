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

/-- Extract loadable segments from a phdr table. Filters by
    `PT_LOAD` and wraps each in `Segment`. The ParsedElf-keyed
    helper `segmentsOf` lives in `Parse.File`. -/
def fromPhdrs (phdrs : Array Spec.Program.Header64) : Array Segment :=
  phdrs.filterMap Segment.fromPhdr?

-- ============================================================================
-- Parse-time well-formedness on PT_LOAD segments.
--
-- `WellFormedB` is the single source of truth — a decidable Bool that
-- runs in `Parse.File.parse` and rejects malformed ELFs at the
-- parse boundary. `WellFormed` is the propositional reading of the
-- same Bool, defined as `WellFormedB = true`, used wherever code
-- carries the witness as a Prop (subtype components, structure
-- fields). They are *the same property* — no bridge to maintain.
--
-- Named accessors for individual clauses (`WellFormed.sorted`,
-- `WellFormed.nonOverlap`, …) live in `Thm/Parse.lean` — they are
-- proof-only and not needed by the production path, which only
-- packs/unpacks the witness as an opaque hypothesis.
--
-- All five clauses are pure properties of header bytes — no loader
-- page-size knowledge. The loader still runs an additional page-
-- aligned check (`Layout.segmentsSortedB`) that can't be evaluated
-- here because it depends on a chosen page size, but the structural
-- pre-conditions for that check are fixed here.
-- ============================================================================

/-- Decidable parse-time well-formedness check on PT_LOAD segments.
    Bundles four gabi-07 mandates plus one de-facto convention,
    each as a finite pairwise/per-entry scan over `segs.size`. Real
    ELFs have <10 PT_LOAD entries, so the O(n²) loops are immaterial.

    Clauses:
    1. **Sorted by `p_vaddr`** — gabi 07 § Program Loading: "PT_LOAD
       entries appear in p_vaddr order in the program header".
    2. **`p_filesz ≤ p_memsz`** — gabi 07 § Program Header (PT_LOAD):
       "p_memsz cannot be smaller than p_filesz". The `[p_filesz,
       p_memsz)` tail is BSS.
    3. **`p_align` is 0 or a power of two** — gabi 07 § Program Header:
       "If p_align is greater than zero, it must be a positive
       integral power of two". `p_align = 0` means "no alignment
       constraint" and is treated as 1 by the loader.
    4. **`p_vaddr ≡ p_offset (mod p_align)`** — gabi 07 § Program
       Header: "p_vaddr should equal p_offset, modulo p_align".
       Specified as SHOULD (not MUST), but `Layout.fileOffsetPaged`
       relies on it; without it `mmap(2)` would map the wrong file
       bytes for page-unaligned segments.
    5. **`[p_vaddr, p_vaddr + p_memsz)` ranges pairwise disjoint** —
       *de facto* convention, NOT gabi-mandated. Every linker
       produces it; `Map.lean`'s `MAP_FIXED` mmap relies on the
       stronger page-aligned form (`Layout.segmentsSortedB`) for
       correctness, which follows from this raw non-overlap together
       with `p_align ≥ pageSize` and segment-start page-alignment
       (also de facto). -/
def WellFormedB (segs : Array Segment) : Bool :=
  let pair (p : Segment → Segment → Bool) : Bool :=
    (List.range segs.size).all fun i =>
      (List.range segs.size).all fun j =>
        !decide (i < j) ||
          (match segs[i]?, segs[j]? with
           | some s, some s' => p s s'
           | _, _ => true)
  let perEntry (p : Segment → Bool) : Bool :=
    (List.range segs.size).all fun i =>
      match segs[i]? with
      | some s => p s
      | none   => true
  pair (fun s s' => decide (s.phdr.p_vaddr ≤ s'.phdr.p_vaddr)) &&
  perEntry (fun s => decide (s.phdr.p_filesz ≤ s.phdr.p_memsz)) &&
  perEntry (fun s =>
    let a := s.phdr.p_align
    decide (a = 0) || decide ((a &&& (a - 1)) = 0)) &&
  perEntry (fun s =>
    let a := s.phdr.p_align
    decide (a = 0) ||
    decide (s.phdr.p_vaddr % a = s.phdr.p_offset % a)) &&
  pair (fun s s' =>
    decide (s.phdr.p_vaddr + s.phdr.p_memsz ≤ s'.phdr.p_vaddr))

/-- Propositional reading of `WellFormedB`. The witness `Parse.File.parse`
    packs into the parsed-ELF subtype and that `LoadedObject.elf_wf`
    carries. Definitionally `WellFormedB segs = true`, so the runtime
    check decides this Prop with no separate bridge. Named accessors
    for individual clauses (`sorted`, `nonOverlap`, …) live in
    `Thm/Parse.lean`. -/
abbrev WellFormed (segs : Array Segment) : Prop := WellFormedB segs = true

/-- The empty segment array is well-formed by `decide` on a closed
    term. Used by synthetic ELFs in `Fixtures` (which have no PT_LOAD
    entries); inlining `decide` at those sites fails because the
    surrounding parameters leave the goal open and `decide +revert`
    quantifies over an infinite type. -/
theorem WellFormed_nil : WellFormed (#[] : Array Segment) := by decide

end LeanLoad.Parse.Segment

/-
PT_LOAD segment helpers — *parse/IO-side* logic on top of the
`Segment` refinement defined in `Spec.Program`.

The Spec/ side owns:
  - `Spec.Program.Segment` (refinement type: a `Header64` with
    `p_type = PT_LOAD`).
  - The Prop-level invariants `Spec.Program.{Sorted, FileszLeMemsz,
    AlignPow2, AlignCong, NonOverlap}` — gabi-07 mandates plus one
    de-facto convention, as plain quantifiers.

This file owns:
  - The smart constructor `Segment.fromPhdr?` (runtime PT_LOAD check).
  - The trivial accessors `Segment.fileOff`, `Segment.fileLen`.
  - The phdr-table → segments helper `fromPhdrs`.
  - The decidable Bool mirror `WellFormedB` and the propositional
    alias `WellFormed := WellFormedB segs = true`.

**Loader-level views** (`vaddr`, `length`, `prot`, `endAddr`, …) —
which page-align addresses for `mmap(2)` and translate `PF_*` to
POSIX `PROT_*` — live in `LeanLoad.Layout`. Those are decisions the
loader makes, not properties the spec dictates.

Methods on `Segment` (`fromPhdr?`, `fileOff`, `fileLen`) live in
the `Spec.Program.Segment` namespace so dot notation works wherever
the type is in scope. Functions over `Array Segment` (`fromPhdrs`,
`WellFormedB`, `WellFormed`) live in the `Parse.Segment` namespace.
-/

import LeanLoad.Spec.Program

-- ============================================================================
-- Methods on `Spec.Program.Segment` — the smart constructor and the
-- trivial header-field accessors. Defined in this namespace so
-- `s.fromPhdr?` / `s.fileLen` dot notation resolves on the type.
-- ============================================================================

namespace LeanLoad.Spec.Program.Segment

/-- Lift a `Header64` into a `Segment` if it is `PT_LOAD`. -/
def fromPhdr? (ph : Header64) : Option Segment :=
  if h : ph.p_type = PT_LOAD then some ⟨ph, h⟩ else none

/-- File offset to start copying bytes from. -/
def fileOff (s : Segment) : UInt64 := s.phdr.p_offset

/-- Number of bytes to copy (≤ memory length; remainder is BSS). -/
def fileLen (s : Segment) : UInt64 := s.phdr.p_filesz

end LeanLoad.Spec.Program.Segment

namespace LeanLoad.Parse.Segment

open LeanLoad
open LeanLoad.Spec
open LeanLoad.Spec.Program (Segment)

/-- Extract loadable segments from a phdr table. Filters by
    `PT_LOAD` and wraps each in `Segment`. The ParsedElf-keyed
    helper `segmentsOf` lives in `Parse.File`. -/
def fromPhdrs (phdrs : Array Spec.Program.Header64) : Array Segment :=
  phdrs.filterMap Segment.fromPhdr?

-- ============================================================================
-- Parse-time well-formedness on PT_LOAD segments.
--
-- `WellFormedB` is the single source of truth — a decidable Bool
-- that runs in `Parse.File.validate` and rejects malformed ELFs at
-- the parse boundary. `WellFormed` is the propositional reading,
-- defined as `WellFormedB = true`, used wherever code carries the
-- witness as a Prop (subtype components, structure fields). They
-- are *the same property* — no bridge to maintain.
--
-- The Prop-level statements of each clause (`Spec.Program.Sorted`,
-- `Spec.Program.NonOverlap`, …) live in `Spec/Program.lean` —
-- they're transcriptions of gabi-07 mandates. Theorems in
-- `Thm/Parse.lean` extract each one from a `WellFormed` witness.
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

    Each clause's gabi-07 reference and meaning lives next to the
    Prop-level statement in `Spec.Program` (`Sorted`,
    `FileszLeMemsz`, `AlignPow2`, `AlignCong`, `NonOverlap`). -/
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
    `Thm/Parse.lean` and produce `Spec.Program.*` Props. -/
abbrev WellFormed (segs : Array Segment) : Prop := WellFormedB segs = true

/-- The empty segment array is well-formed by `decide` on a closed
    term. Used by synthetic ELFs in `Fixtures` (which have no PT_LOAD
    entries); inlining `decide` at those sites fails because the
    surrounding parameters leave the goal open and `decide +revert`
    quantifies over an infinite type. -/
theorem WellFormed_nil : WellFormed (#[] : Array Segment) := by decide

section Example
open LeanLoad.Spec.Program (Header64 PT_LOAD PF_R PF_W)

/-- Build a PT_LOAD segment with named arguments — each example
    below uses `(vaddr := …)` syntax so the call site is readable
    even though the function takes 5 `UInt64`s. -/
private def mkSeg (vaddr memsz filesz align offset : UInt64) : Segment :=
  ⟨{ (default : Header64) with
       p_type := PT_LOAD,
       p_vaddr := vaddr, p_memsz := memsz, p_filesz := filesz,
       p_align := align, p_offset := offset,
       p_flags := PF_R ||| PF_W }, rfl⟩

-- A small library of segments named after the property they
-- demonstrate. Each one is annotated with the clause it exercises.
-- Examples below combine them; reading a guard's input list reads
-- as English ("text + data" / "text + overlapping" / …).

/-- A normal text segment: `[0x1000, 0x2000)` in memory, `0x800`
    bytes from the file, page-aligned and congruent. Baseline for
    "well-formed" examples. -/
private def textSeg : Segment :=
  mkSeg (vaddr := 0x1000) (memsz := 0x1000) (filesz := 0x800)
        (align := 0x1000) (offset := 0x1000)

/-- A normal data segment that follows `textSeg` cleanly:
    `[0x3000, 0x3500)` in memory, fully file-backed. -/
private def dataSeg : Segment :=
  mkSeg (vaddr := 0x3000) (memsz := 0x500) (filesz := 0x500)
        (align := 0x1000) (offset := 0x2000)

/-- Starts at 0x1800, inside `textSeg`'s `[0x1000, 0x2000)` —
    overlapping the first one. Used to exercise the `NonOverlap`
    clause. -/
private def overlappingSeg : Segment :=
  mkSeg (vaddr := 0x1800) (memsz := 0x500) (filesz := 0x500)
        (align := 0x1000) (offset := 0x1800)

/-- `p_filesz` (0x200) exceeds `p_memsz` (0x100) — exercises the
    `FileszLeMemsz` clause. -/
private def filesizeTooBig : Segment :=
  mkSeg (vaddr := 0x1000) (memsz := 0x100) (filesz := 0x200)
        (align := 0x1000) (offset := 0x1000)

/-- `p_align = 3` is not a power of two — exercises `AlignPow2`. -/
private def badAlign : Segment :=
  mkSeg (vaddr := 0x1000) (memsz := 0x100) (filesz := 0x100)
        (align := 3) (offset := 0x1000)

/-- `p_offset = 0x1004`, `p_vaddr = 0x1000`, both `mod 0x1000` ⇒
    `0x4 ≠ 0x0`. Exercises the `AlignCong` clause (gabi-07 SHOULD). -/
private def badCongruence : Segment :=
  mkSeg (vaddr := 0x1000) (memsz := 0x100) (filesz := 0x100)
        (align := 0x1000) (offset := 0x1004)

-- ============================================================================
-- Examples — read each input list as a sentence describing the case.
-- ============================================================================

-- Two well-formed PT_LOADs back-to-back.
#guard WellFormedB #[textSeg, dataSeg] = true

-- Empty array is vacuously well-formed.
#guard WellFormedB (#[] : Array Segment) = true

-- Out of order (data first, then text) → fails `Sorted`.
#guard WellFormedB #[dataSeg, textSeg] = false

-- Overlap (text + a segment that starts inside text) → fails `NonOverlap`.
#guard WellFormedB #[textSeg, overlappingSeg] = false

-- filesz > memsz → fails `FileszLeMemsz`.
#guard WellFormedB #[filesizeTooBig] = false

-- p_align = 3 (not a power of 2) → fails `AlignPow2`.
#guard WellFormedB #[badAlign] = false

-- p_vaddr % align ≠ p_offset % align → fails `AlignCong`.
#guard WellFormedB #[badCongruence] = false
end Example

end LeanLoad.Parse.Segment

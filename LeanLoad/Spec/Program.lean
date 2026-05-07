/-
Program header table — gabi 07 spec.

Spec: gabi 07 (`third_party/gabi/docsrc/elf/07-pheader.rst`).

The program header table is the load-time view of an ELF file: each
entry describes a segment the system needs to prepare the process
image. Types and constants only — parser in `LeanLoad.Parse.Program`.
-/

namespace LeanLoad.Spec.Program

-- ============================================================================
-- Constants — gabi 07 § Program Header, Tables: Segment Types, Segment Flag Bits
-- ============================================================================

-- p_type
def PT_NULL    : UInt32 := 0
def PT_LOAD    : UInt32 := 1
def PT_DYNAMIC : UInt32 := 2
def PT_INTERP  : UInt32 := 3
def PT_NOTE    : UInt32 := 4
def PT_SHLIB   : UInt32 := 5
def PT_PHDR    : UInt32 := 6
def PT_TLS     : UInt32 := 7

-- p_flags (segment permission bits)
def PF_X : UInt32 := 0x1
def PF_W : UInt32 := 0x2
def PF_R : UInt32 := 0x4

-- ============================================================================
-- Program header — gabi 07 § Program Header Entry (Elf64_Phdr)
-- ============================================================================

/-- 64-bit program header entry. Layout matches `Elf64_Phdr` in gabi 07. -/
structure Header64 where
  p_type   : UInt32
  p_flags  : UInt32
  p_offset : UInt64
  p_vaddr  : UInt64
  p_paddr  : UInt64
  p_filesz : UInt64
  p_memsz  : UInt64
  p_align  : UInt64
  deriving Repr, Inhabited

/-- Size of one entry on disk (gabi 07: 4+4+8*6 = 56). -/
def entrySize : Nat := 56

-- ============================================================================
-- Loadable segment (PT_LOAD-typed phdr) — refinement of `Header64`.
--
-- `Segment` is a `Header64` carrying a proof that `p_type = PT_LOAD`.
-- Pure data — the smart constructor `Parse.Segment.fromPhdr?` and
-- the decidable runtime check `Parse.Segment.WellFormedB` live in
-- `Parse/Segment.lean`. The Prop-level invariants below are
-- transcriptions of gabi-07 mandates (plus one de-facto convention)
-- and live alongside the type they constrain.
-- ============================================================================

/-- A loadable segment: a `Header64` whose `p_type = PT_LOAD`. -/
structure Segment where
  phdr   : Header64
  isLoad : phdr.p_type = PT_LOAD
  deriving Repr

-- ============================================================================
-- gabi-07 well-formedness on PT_LOAD segments.
--
-- These are the *Prop-level* statements: pure quantifiers over the
-- segment array, no decision procedure. The decidable `WellFormedB`
-- mirror is in `Parse/Segment.lean`; the bridge (`WellFormed witness
-- → these props`) lives in `Thm/Parse.lean`.
-- ============================================================================

/-- gabi 07 § Program Loading: PT_LOAD entries appear in `p_vaddr` order. -/
def Sorted (segs : Array Segment) : Prop :=
  ∀ i j (_ : i < segs.size) (_ : j < segs.size),
    i < j → segs[i].phdr.p_vaddr ≤ segs[j].phdr.p_vaddr

/-- gabi 07 § Program Header (PT_LOAD): "p_memsz cannot be smaller
    than p_filesz". The `[p_filesz, p_memsz)` tail is BSS. -/
def FileszLeMemsz (segs : Array Segment) : Prop :=
  ∀ i (_ : i < segs.size), segs[i].phdr.p_filesz ≤ segs[i].phdr.p_memsz

/-- gabi 07 § Program Header: "If p_align is greater than zero, it
    must be a positive integral power of two". `p_align = 0` means
    "no alignment constraint" and is treated as 1 by the loader. -/
def AlignPow2 (segs : Array Segment) : Prop :=
  ∀ i (_ : i < segs.size),
    segs[i].phdr.p_align = 0 ∨
    (segs[i].phdr.p_align &&& (segs[i].phdr.p_align - 1)) = 0

/-- gabi 07 § Program Header: "p_vaddr should equal p_offset, modulo
    p_align". Specified as SHOULD, not MUST, but the loader's
    `Layout.fileOffsetPaged` relies on it. -/
def AlignCong (segs : Array Segment) : Prop :=
  ∀ i (_ : i < segs.size),
    segs[i].phdr.p_align = 0 ∨
    segs[i].phdr.p_vaddr % segs[i].phdr.p_align =
      segs[i].phdr.p_offset % segs[i].phdr.p_align

/-- *De facto*, not gabi-mandated: PT_LOAD `[p_vaddr, p_vaddr +
    p_memsz)` ranges are pairwise disjoint. Every linker produces
    this; `Map.lean`'s `MAP_FIXED` mmap relies on the stronger
    page-aligned form (`Layout.segmentsSortedB`) for correctness. -/
def NonOverlap (segs : Array Segment) : Prop :=
  ∀ i j (_ : i < segs.size) (_ : j < segs.size),
    i < j →
    segs[i].phdr.p_vaddr + segs[i].phdr.p_memsz ≤ segs[j].phdr.p_vaddr

end LeanLoad.Spec.Program

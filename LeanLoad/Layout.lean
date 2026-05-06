/-
Layout — per-object segment arrangement, pure.

Layout consumes `Array Parse.Segment.Segment` (typed `PT_LOAD`s)
that the parser already produced, and assigns each object an mmap
base + builds the cross-object plan that Map / Reloc / Apply / Exec
consume. Validation that the parser-produced segments are well-
formed (sorted, non-overlapping) happens at the boundary in
`g.layouts`, which returns `Except String (Array ObjectLayout)`.

Dependency ordering lives in `LeanLoad.Order` (gabi 08); this file
covers gabi 07 positional concerns (base assignment, span over
loadable segments).
-/

import LeanLoad.Parse.Segment
import LeanLoad.DiscoverPlan
import LeanLoad.Spec.Program

namespace LeanLoad.Layout

open LeanLoad
open LeanLoad.Spec
open LeanLoad.Discover
open LeanLoad.Parse.Segment

-- ============================================================================
-- PF_* → PROT_* translation (loader-level: gabi `PF_*` → POSIX `PROT_*`)
-- ============================================================================

/-- Translate program-header permissions (gabi 07 § Segment Permissions)
    to the corresponding `PROT_*` bits for `mprotect`. The bit
    positions are swapped between PF_* and PROT_*: `PF_X=1, PF_W=2,
    PF_R=4` vs `PROT_READ=1, PROT_WRITE=2, PROT_EXEC=4`, so each
    flag must be translated explicitly. `PROT_*` is POSIX, not gabi —
    this is loader-level. -/
def protOfFlags (pflags : UInt32) : UInt32 :=
  let r := if (pflags &&& Program.PF_R) != 0 then (1 : UInt32) else 0
  let w := if (pflags &&& Program.PF_W) != 0 then (2 : UInt32) else 0
  let x := if (pflags &&& Program.PF_X) != 0 then (4 : UInt32) else 0
  r ||| w ||| x

#guard protOfFlags (Program.PF_R ||| Program.PF_X) = 5
#guard protOfFlags (Program.PF_R ||| Program.PF_W) = 3
#guard protOfFlags Program.PF_R = 1
#guard protOfFlags (Program.PF_R + Program.PF_X) = 5

-- ============================================================================
-- Page alignment helpers (loader-level: required by mmap(2))
-- ============================================================================

/-- Round `x` down to a multiple of `align`. `align` must be a power of two
    (or zero, treated as 1). -/
def alignDown (x align : UInt64) : UInt64 :=
  if align == 0 then x else x - (x % align)

/-- Round `x` up to a multiple of `align`. -/
def alignUp (x align : UInt64) : UInt64 :=
  if align == 0 then x else alignDown (x + align - 1) align

#guard alignDown 0x1234 0x1000 == 0x1000
#guard alignUp 0x1234 0x1000 == 0x2000
#guard alignDown 0x1000 0x1000 == 0x1000
#guard alignUp   0x1000 0x1000 == 0x1000
#guard alignDown 0x1234 0 == 0x1234
#guard alignUp   0x1234 0 == 0x1234

end LeanLoad.Layout

-- ============================================================================
-- Loader-level views of a `Segment` — page-aligned mmap addresses,
-- POSIX `PROT_*` translation. Defined under the `Parse.Segment.Segment`
-- namespace so dot notation works (`s.vaddr`, `s.length`, …) wherever
-- this file is imported. The parse-level type stays minimal; these
-- are extension methods.
-- ============================================================================

namespace LeanLoad.Parse.Segment.Segment

open LeanLoad.Layout

/-- Effective alignment (treats `p_align = 0` as 1). -/
private def effectiveAlign (s : Segment) : UInt64 :=
  if s.phdr.p_align == 0 then 1 else s.phdr.p_align

/-- Page-aligned mmap base. -/
def vaddr (s : Segment) : UInt64 := alignDown s.phdr.p_vaddr s.effectiveAlign

/-- mmap length in bytes (page-aligned over the full memory range). -/
def length (s : Segment) : UInt64 :=
  alignUp (s.phdr.p_vaddr + s.phdr.p_memsz) s.effectiveAlign - s.vaddr

/-- POSIX `PROT_*` bits for `mprotect`, translated from gabi `PF_*`. -/
def prot (s : Segment) : UInt32 := protOfFlags s.phdr.p_flags

/-- Offset within the mapped region where copied bytes begin (handles
    the case `p_vaddr` is not page-aligned). -/
def pageInset (s : Segment) : UInt64 := s.phdr.p_vaddr - s.vaddr

/-- Page-aligned length of the file-backed mmap range: covers
    `pageInset + fileLen` rounded up. `≤ length` (BSS tail extends
    beyond). -/
def fileLenPaged (s : Segment) : UInt64 :=
  alignUp (s.pageInset + s.fileLen) s.effectiveAlign

/-- Page-aligned file offset for `mmap(2)`. Equals `p_offset -
    pageInset` for gabi-07-conforming ELFs (the congruence
    `p_vaddr ≡ p_offset (mod p_align)`). -/
def fileOffsetPaged (s : Segment) : UInt64 :=
  alignDown s.phdr.p_offset s.effectiveAlign

/-- One past the last byte of the segment's mmap'd range. -/
def endAddr (s : Segment) : UInt64 := s.vaddr + s.length

/-- Two segments are disjoint when their `[vaddr, endAddr)` ranges don't overlap. -/
def disjoint (s₁ s₂ : Segment) : Prop :=
  s₁.endAddr ≤ s₂.vaddr ∨ s₂.endAddr ≤ s₁.vaddr

end LeanLoad.Parse.Segment.Segment

namespace LeanLoad.Layout

open LeanLoad
open LeanLoad.Spec
open LeanLoad.Discover
open LeanLoad.Parse.Segment

-- Page-aligned vaddr at 0x1000, fits in one 0x1000 page → no inset.
#guard
  let s : Segment := ⟨{ (default : Program.Header64) with
    p_type := Program.PT_LOAD,
    p_vaddr := 0x1000, p_memsz := 0x800, p_filesz := 0x800,
    p_align := 0x1000, p_flags := Program.PF_R ||| Program.PF_X,
    p_offset := 0x1000 }, by decide⟩
  s.vaddr = 0x1000 ∧ s.length = 0x1000 ∧ s.pageInset = 0 ∧ s.prot = 5
-- Unaligned vaddr 0x1234 with 0x1000 alignment.
#guard
  let s : Segment := ⟨{ (default : Program.Header64) with
    p_type := Program.PT_LOAD,
    p_vaddr := 0x1234, p_memsz := 0x100, p_filesz := 0x100,
    p_align := 0x1000, p_flags := Program.PF_R ||| Program.PF_W,
    p_offset := 0x1234 }, by decide⟩
  s.vaddr = 0x1000 ∧ s.length = 0x1000 ∧ s.pageInset = 0x234 ∧ s.prot = 3
-- p_align = 0 ⇒ identity.
#guard
  let s : Segment := ⟨{ (default : Program.Header64) with
    p_type := Program.PT_LOAD,
    p_vaddr := 0x42, p_memsz := 0x10, p_filesz := 0x10,
    p_align := 0, p_flags := Program.PF_R }, by decide⟩
  s.vaddr = 0x42 ∧ s.length = 0x10 ∧ s.pageInset = 0
-- BSS tail: memsz > filesz.
#guard
  let s : Segment := ⟨{ (default : Program.Header64) with
    p_type := Program.PT_LOAD,
    p_vaddr := 0x2000, p_memsz := 0x800, p_filesz := 0x200,
    p_align := 0x1000, p_flags := Program.PF_R ||| Program.PF_W,
    p_offset := 0x2000 }, by decide⟩
  s.fileLen = 0x200 ∧ s.length = 0x1000

-- ============================================================================
-- ObjectLayout — per-object plan with chosen base.
-- ============================================================================

/-- Layout for a single loaded object.

    `base` is the absolute mmap address at which the object's
    segments will be placed. For `ET_EXEC` (vaddrs already absolute)
    `base = 0` and Map uses `s.vaddr` directly. For `ET_DYN`, Layout
    picks `base = dynAnchor + cumulative_offset` so each object lives
    in its own non-overlapping slot starting at `dynAnchor`; Map then
    uses `MAP_FIXED` everywhere — no kernel-chosen bases.

    There's no `objectIdx` field — a layout is identified by its
    position in the parent array (`g.layouts.val[i]` corresponds to
    `g.objects[i]`), so storing the index would be redundant state. -/
structure ObjectLayout where
  /-- Absolute mmap base address chosen by Layout. -/
  base      : UInt64
  segments  : Array Segment
  /-- The `e_entry` field. `none` for objects we never enter
      (e.g. shared libraries). -/
  entry     : Option UInt64
  /-- True for the main executable. -/
  isMain    : Bool
  deriving Repr

/-- Hardcoded anchor for the first `ET_DYN` object. Subsequent
    `ET_DYN` objects stack above it. Picked to be high enough to
    avoid colliding with the host process's typical mappings on
    x86-64 / aarch64 (heap, libc, etc., usually in the low GB). -/
def dynAnchor : UInt64 := 0x80000000

/-- The contiguous span an array of segments needs (relative to the
    object's base). Used by `assignBases` (with `segmentsOf elf`) to
    size each `ET_DYN` object's arena slot, and by `Map` (with
    `lyt.segments`) for the per-object anon reservation. -/
def objectSpan (segments : Array Segment) : UInt64 :=
  segments.foldl (init := 0) fun acc s => max acc s.endAddr

/-- The contiguous span of one object's segments — convenience
    accessor for `objectSpan lyt.segments`, enables `lyt.span`. -/
def ObjectLayout.span (lyt : ObjectLayout) : UInt64 :=
  objectSpan lyt.segments

/-- Layout for a single parsed ELF. `base` is decided by the
    enclosing `DepGraph.layouts` (anchor + cumulative for `ET_DYN`,
    0 for `ET_EXEC`). -/
def objectLayout (isMain : Bool) (base : UInt64)
    (elf : Parse.File.ParsedElf) : ObjectLayout :=
  let entry := if isMain then some elf.header.e_entry else none
  { base, segments := segmentsOf elf, entry, isMain }

/-- Segments are pairwise disjoint (`[vaddr, endAddr)` ranges don't overlap). -/
def ObjectLayout.segmentsPairwiseDisjoint (lyt : ObjectLayout) : Prop :=
  ∀ i j (_ : i < lyt.segments.size) (_ : j < lyt.segments.size),
    i ≠ j → Segment.disjoint lyt.segments[i] lyt.segments[j]

/-- Segments are sorted by `vaddr` with each one's end ≤ the next one's start.
    The clean precondition under which pairwise disjointness follows; the
    real-ELF discharge comes from `Parse.Segment.wellFormed`. -/
def ObjectLayout.segmentsSorted (lyt : ObjectLayout) : Prop :=
  ∀ i j (_ : i < lyt.segments.size) (_ : j < lyt.segments.size),
    i < j → lyt.segments[i].endAddr ≤ lyt.segments[j].vaddr

-- ============================================================================
-- Layout-stage output is `Array ObjectLayout` (one entry per object,
-- in `DepGraph.objects` order). `g.layouts` returns
-- `Except String (Array ObjectLayout)` — the well-formedness check
-- runs here at the boundary; a malformed ELF surfaces as an error
-- before Map (which would otherwise produce undefined behaviour
-- against `MAP_FIXED`).
--
-- Init/fini order (gabi 08) is computed separately in `LeanLoad.Order`
-- and threaded directly to `Exec.runInits` — purely gabi-07 here
-- (segment placement). Relocations are not part of `Layout` either;
-- they depend on actual chosen bases and are computed post-Map by
-- `LeanLoad.Reloc.plan`.
-- ============================================================================

/-- Assign an mmap base to each object in BFS order. `ET_EXEC`
    objects keep `0`; `ET_DYN` objects start at `dynAnchor` and
    stack by `alignUp objectSpan 0x1000`. -/
def assignBases (g : DepGraph) : Array UInt64 := Id.run do
  let mut bases : Array UInt64 := Array.mkEmpty g.objects.size
  let mut cursor : UInt64 := dynAnchor
  for h : i in [:g.objects.size] do
    let obj := g.objects[i]
    let isExec := obj.elf.header.e_type = 2
    let base := if isExec then 0 else cursor
    bases := bases.push base
    if !isExec then
      cursor := cursor + alignUp (objectSpan (segmentsOf obj.elf)) 0x1000
  return bases

end LeanLoad.Layout

namespace LeanLoad.Discover.DepGraph

open LeanLoad.Layout
open LeanLoad.Parse.Segment

/-- Build the per-object layouts for a discovered dep graph. The
    first object (index 0) is main. Each ELF is checked for
    well-formed segments (sorted by `vaddr` with non-overlapping
    ranges); a malformed ELF surfaces as `error`.

    Returns a sized subtype `{ a : Array ObjectLayout // a.size =
    g.objects.size }`: the size invariant is in the type, so
    downstream consumers (`Map.mapAll`, `Reloc.plan`) get the size
    for free without runtime checks. -/
def layouts (g : DepGraph) : Except String { a : Array ObjectLayout // a.size = g.objects.size } :=
  match g.objects.findIdx? (fun obj => !wellFormed obj.elf) with
  | some i =>
    let name := (g.objects[i]?.map (·.name)).getD "?"
    .error s!"layouts: object[{i}] ({name}) has malformed PT_LOAD segments"
  | none =>
    let bases := assignBases g
    let arr := g.objects.mapIdx fun i obj =>
      objectLayout (i = 0) (bases[i]?.getD 0) obj.elf
    .ok ⟨arr, by simp [arr]⟩

end LeanLoad.Discover.DepGraph

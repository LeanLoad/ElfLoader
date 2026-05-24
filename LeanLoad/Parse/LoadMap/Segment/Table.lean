/-
Checked PT_LOAD segment arrays.

`Segment.Basic` owns one segment's byte fields and per-segment invariants.
This file owns the checked array wrapper plus predicates whose subject is the
whole PT_LOAD array.

Spec: gabi 07 (`third_party/gabi/docsrc/elf/07-pheader.rst`) § Program Loading.
-/

import LeanLoad.Parse.LoadMap.Segment.Basic

namespace LeanLoad.Parse

-- ============================================================================
-- PT_LOAD-array well-formedness — the per-pair gabi-07 invariants on
-- `Array (Segment fileSize)`. Per-segment invariants are validated by
-- `Segment.ofPhdr`.
--
-- Spec: gabi 07 § Program Loading. These are *spec-level* (gabi eaddr/memsz
-- ordering); page-aligned non-overlap is a separate runtime check via
-- `Layout.SegmentLayout` over `SegmentLayout`s.
-- ============================================================================

namespace SegmentTable

/-- gabi 07 § Program Loading: PT_LOAD entries appear in `p_vaddr` order. -/
def Sorted {fileSize : ByteSize} (segs : Array (Segment fileSize)) : Prop :=
  ∀ i, ∀ _ : i < segs.size, ∀ j, ∀ _ : j < segs.size,
    i < j → segs[i].eaddr.toNat ≤ segs[j].eaddr.toNat

/-- *De facto*, not gabi-mandated: PT_LOAD `[p_vaddr, p_vaddr + p_memsz)`
    ranges are pairwise disjoint. -/
def NonOverlap {fileSize : ByteSize} (segs : Array (Segment fileSize)) : Prop :=
  ∀ i, ∀ _ : i < segs.size, ∀ j, ∀ _ : j < segs.size,
    i < j → segs[i].eaddr.toNat + segs[i].memsz.toNat ≤ segs[j].eaddr.toNat

end SegmentTable

/-- Checked PT_LOAD segment array. `items` keeps the phdr order, while `sorted`
    / `nonOverlap` are the array-level facts established at checked-parse time. -/
structure SegmentTable (fileSize : ByteSize) where
  private mk ::
  items      : Array (Segment fileSize)
  sorted     : SegmentTable.Sorted items
  nonOverlap : SegmentTable.NonOverlap items
  deriving Repr

namespace SegmentTable

/-- A ELF-address range contained in one checked segment satisfying `need`
    (for example, executable or readable). -/
structure EaddrRangeIn {fileSize : ByteSize} (segments : SegmentTable fileSize)
    (need : Segment fileSize → Prop)
    (addr : Eaddr) (len : ByteSize) where
  index    : Fin segments.items.size
  contains : Segment.ContainsEaddrRange segments.items[index] addr len
  permits  : need segments.items[index]
  deriving Repr

/-- A file-offset range contained in one checked segment satisfying `need`. -/
structure FileRangeIn {fileSize : ByteSize} (segments : SegmentTable fileSize)
    (need : Segment fileSize → Prop)
    (off : FileOff) (len : ByteSize) where
  index    : Fin segments.items.size
  contains : Segment.ContainsFileRange segments.items[index] off len
  permits  : need segments.items[index]
  deriving Repr

/-- A ELF-address range that is backed by file bytes in one checked segment
    satisfying `need`. Dynamic-table pointers use this rather than plain memory
    containment so they cannot point into BSS. -/
structure FileBackedEaddrRangeIn {fileSize : ByteSize} (segments : SegmentTable fileSize)
    (need : Segment fileSize → Prop)
    (addr : Eaddr) (len : ByteSize) where
  index    : Fin segments.items.size
  contains : Segment.ContainsFileBackedEaddrRange segments.items[index] addr len
  permits  : need segments.items[index]
  deriving Repr

/-- Point membership in one checked segment satisfying `need`. Kept as an
    `abbrev` so legacy existential proofs can still destruct it directly. -/
abbrev ContainsEaddr {fileSize : ByteSize} (segments : SegmentTable fileSize)
    (need : Segment fileSize → Prop) (addr : Eaddr) : Prop :=
  ∃ i, ∃ h : i < segments.items.size,
    need (segments.items[i]'h) ∧ Segment.ContainsEaddr (segments.items[i]'h) addr

abbrev ExecAddr {fileSize : ByteSize} (segments : SegmentTable fileSize) (addr : Eaddr) : Prop :=
  ContainsEaddr segments (fun s => s.perm.exec) addr

abbrev ReadEaddrRange {fileSize : ByteSize} (segments : SegmentTable fileSize) (addr : Eaddr)
    (len : ByteSize) :=
  EaddrRangeIn segments (fun s => s.perm.read) addr len

abbrev ExecEaddrRange {fileSize : ByteSize} (segments : SegmentTable fileSize) (addr : Eaddr)
    (len : ByteSize) :=
  EaddrRangeIn segments (fun s => s.perm.exec) addr len

abbrev ReadFileRange {fileSize : ByteSize} (segments : SegmentTable fileSize) (off : FileOff)
    (len : ByteSize) :=
  FileRangeIn segments (fun s => s.perm.read) off len

abbrev AnyFileBackedEaddrRange {fileSize : ByteSize} (segments : SegmentTable fileSize)
    (addr : Eaddr) (len : ByteSize) :=
  FileBackedEaddrRangeIn segments (fun _ => True) addr len

abbrev ReadFileBackedEaddrRange {fileSize : ByteSize} (segments : SegmentTable fileSize)
    (addr : Eaddr) (len : ByteSize) :=
  FileBackedEaddrRangeIn segments (fun s => s.perm.read) addr len

/-- Empty checked segment array. Useful for tests and synthetic Elfs. -/
def empty {fileSize : ByteSize} : SegmentTable fileSize :=
  { items := #[],
    sorted := by
      intro i h_i
      simp at h_i
    nonOverlap := by
      intro i h_i
      simp at h_i }

/-- Check an array of PT_LOAD segments into the witnessed `SegmentTable` type. -/
def ofArray {fileSize : ByteSize} (items : Array (Segment fileSize)) :
    Except String (SegmentTable fileSize) :=
  letI : Decidable (Sorted items) := by
    unfold Sorted
    infer_instance
  letI : Decidable (NonOverlap items) := by
    unfold NonOverlap
    infer_instance
  if h_sorted : Sorted items then
    if h_nonOverlap : NonOverlap items then
      .ok { items, sorted := h_sorted, nonOverlap := h_nonOverlap }
    else
      .error "parse: PT_LOAD segments overlap \
        (non-overlap is de facto from linker)"
  else
    .error "parse: PT_LOAD segments not sorted \
      (gabi-07 § Program Loading: sort by p_vaddr)"

end SegmentTable

-- ============================================================================
-- ProgramHeader mapping — when the runtime emits `AT_PHDR`, a PT_LOAD segment must
-- file-back the program-header table. The value is computed by translating
-- `e_phoff` through the covering segment, not by assuming `p_vaddr = p_offset`.
-- ============================================================================

/-- The PT_LOAD segment `s` file-backs the program-header table at file offset
    `phoff` of byte length `nbytes`. -/
def coversProgramHeaders {fileSize : ByteSize} (s : Segment fileSize) (phoff : FileOff)
    (nbytes : Nat) : Prop :=
  s.offset.toNat ≤ phoff.toNat ∧
  phoff.toNat + nbytes ≤ s.offset.toNat + s.filesz.toNat

/-- Checked program-header table mapping for `AT_PHDR`. This carries the segment index
    needed to translate the table's file offset into its loaded ELF address. -/
inductive ProgramHeaderMap {fileSize : ByteSize} (segments : SegmentTable fileSize)
    (phoff : FileOff) (nbytes : Nat) where
  | empty (isEmpty : nbytes = 0)
  | mapped (index : Fin segments.items.size)
      (covers : coversProgramHeaders segments.items[index] phoff nbytes)
  deriving Repr

namespace ProgramHeaderMap

/-- Virtual address of the program-header table in the loaded image, relative to
    the object's base. For `phnum = 0`, `AT_PHDR` is unused and this returns 0. -/
def eaddr {fileSize : ByteSize} {segments : SegmentTable fileSize} {phoff : FileOff} {nbytes : Nat}
    (m : ProgramHeaderMap segments phoff nbytes) : Eaddr :=
  match m with
  | .empty _ => 0
  | .mapped index _ => segments.items[index].eaddrOfFileOff phoff

/-- Build a checked program-header table mapping by searching the checked PT_LOAD array. -/
def ofSegments {fileSize : ByteSize} (segments : SegmentTable fileSize) (phoff : FileOff) (nbytes : Nat) :
    Except String (ProgramHeaderMap segments phoff nbytes) := Id.run do
  if h_empty : nbytes = 0 then
    return .ok (.empty h_empty)
  for h : i in [:segments.items.size] do
    let index : Fin segments.items.size := ⟨i, h.upper⟩
    let decCovers : Decidable (coversProgramHeaders segments.items[index] phoff nbytes) := by
      unfold coversProgramHeaders
      infer_instance
    match decCovers with
    | .isTrue h_covers => return .ok (.mapped index h_covers)
    | .isFalse _ => pure ()
  return .error s!"phdr table at file offset \
    0x{phoff.toNat} (size {nbytes}) is not file-backed by any PT_LOAD; \
    AT_PHDR cannot be computed"

end ProgramHeaderMap

/-- Checked program-header table metadata needed to emit `AT_PHDR`, `AT_PHENT`,
    and `AT_PHNUM`. The map witness proves the table bytes are file-backed by a
    PT_LOAD segment before runtime computes the loaded address. -/
structure ProgramHeaderTable {fileSize : ByteSize} (segments : SegmentTable fileSize) where
  off : FileOff
  count : UInt16
  map : ProgramHeaderMap segments off (ProgramHeaderSize * count.toNat)
  deriving Repr

namespace ProgramHeaderTable

/-- Virtual address of the program-header table in the loaded image, relative to
    the object's base. For `count = 0`, `AT_PHDR` is unused and this returns 0. -/
def eaddr {fileSize : ByteSize} {segments : SegmentTable fileSize}
    (phdr : ProgramHeaderTable segments) : Eaddr :=
  phdr.map.eaddr

/-- Build checked program-header metadata from ELF header fields and PT_LOADs. -/
def ofSegments {fileSize : ByteSize} (segments : SegmentTable fileSize)
    (off : FileOff) (count : UInt16) : Except String (ProgramHeaderTable segments) := do
  let map ← ProgramHeaderMap.ofSegments segments off (ProgramHeaderSize * count.toNat)
  return { off, count, map }

end ProgramHeaderTable

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
def callTargetInExecSeg {fileSize : ByteSize} (segments : SegmentTable fileSize) (entry : Eaddr) : Prop :=
  entry.val = 0 ∨ SegmentTable.ExecAddr segments entry

end LeanLoad.Parse

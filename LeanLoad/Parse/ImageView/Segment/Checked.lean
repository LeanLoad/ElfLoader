/-
Checked PT_LOAD segment — gabi-07 byte fields and per-segment invariants.

Spec: gabi 07 (`third_party/gabi/docsrc/elf/07-pheader.rst`) § Program
Header.

Carried as struct fields:
  - the originating `ProgramHeader` plus a witness that it is `PT_LOAD`,
  - gabi-07 per-segment invariants (`fileszLeMemsz`, `alignPow2`,
    `alignCong`),
  - typed memory/file range witnesses and the page-layout no-wrap bound that
    let `Plan.SegmentLayout` ignore UInt64 wrap without a platform-sized
    address-space shortcut,
  - the per-segment dynamic relocations grouped by their `coversRela`
    witness.

This file is *gabi-only*. mmap semantics (page-aligned addresses, BSS bounds,
POSIX `PROT_*`) live on `Plan.SegmentLayout`, which couples a segment with its
chosen mmap base.
-/

import LeanLoad.Parse.Dynamic.Reloc.Raw
import LeanLoad.Parse.ImageView.ProgramHeader.Basic

namespace LeanLoad.Parse

-- ============================================================================
-- coversRela — segment-relative containment witness for a rela's
-- 8-byte write window. Pure gabi: bounds the offset relative to
-- `[eaddr, eaddr + memsz)`.
-- ============================================================================

/-- The segment's memory range fully contains an 8-byte write window
    starting at `r_offset`. Conservatively reserves 8 bytes. -/
def coversRela (eaddr : Eaddr) (memsz : ByteSize) (r_offset : Eaddr) : Prop :=
  eaddr.toNat ≤ r_offset.toNat ∧
  r_offset.toNat + 8 ≤ eaddr.toNat + memsz.toNat

instance (eaddr : Eaddr) (memsz : ByteSize) (r_offset : Eaddr) :
    Decidable (coversRela eaddr memsz r_offset) := by
  unfold coversRela; infer_instance

/-- A checked relocation whose 8-byte write window is contained in the segment
    range `[eaddr, eaddr + memsz)`. -/
structure Rela (eaddr : Eaddr) (memsz : ByteSize) where
  raw     : RawRela
  covered : coversRela eaddr memsz raw.r_offset
  deriving Repr

-- ============================================================================
-- Segment — gabi-07 byte fields + invariants. mmap-stage semantics
-- live on `Plan.SegmentLayout`.
-- ============================================================================

/-- A PT_LOAD program header's ELF-address memory range
    `[p_vaddr, p_vaddr + p_memsz)` does not wrap UInt64. -/
structure Segment.EaddrRange (phdr : ProgramHeader) where
  noWrap : phdr.p_vaddr.toNat + phdr.p_memsz.toNat < 2 ^ 64

/-- A PT_LOAD program header's file-backed byte range
    `[p_offset, p_offset + p_filesz)` is contained in the source file. -/
structure Segment.FileImageRange (fileSize : UInt64) (phdr : ProgramHeader) where
  inFile : phdr.p_offset.toNat + phdr.p_filesz.toNat ≤ fileSize.toNat

/-- A PT_LOAD segment: gabi-07 byte fields, the gabi per-segment
    invariants, range/layout no-wrap witnesses, and the dynamic relocations
    grouped by `coversRela` witness. -/
structure Segment where
  /-- Observed size of the file this segment came from. -/
  fileSize : UInt64
  /-- Source program-header row. Its fields stay typed as `Eaddr`,
      `FileOff`, and `ByteSize`; projections below expose those typed
      fields without duplicating data. -/
  phdr   : ProgramHeader
  /-- This checked segment is backed by a `PT_LOAD` phdr. -/
  isLoad : phdr.p_type = .load
  /-- Virtual memory range `[p_vaddr, p_vaddr + p_memsz)`. -/
  eaddrRange : Segment.EaddrRange phdr
  /-- File-backed range `[p_offset, p_offset + p_filesz)`. -/
  fileRange : Segment.FileImageRange fileSize phdr
  /-- gabi 07: `p_filesz ≤ p_memsz`. -/
  fileszLeMemsz : phdr.p_filesz.toNat ≤ phdr.p_memsz.toNat
  /-- gabi 07: `p_align` is `0` or a power of two. -/
  alignPow2 : phdr.p_align = 0 ∨ (phdr.p_align &&& (phdr.p_align - 1)) = 0
  /-- gabi 07: `p_vaddr ≡ p_offset (mod p_align)`. -/
  alignCong : phdr.p_align = 0 ∨ phdr.p_vaddr.val % phdr.p_align = phdr.p_offset.val % phdr.p_align
  /-- No UInt64 wrap when page layout rounds `[p_vaddr, p_vaddr + p_memsz)`
      by the effective alignment used by `Plan.SegmentLayout`. This is a
      loader arithmetic bound, not a 48-bit platform policy. -/
  pageLayoutNoWrap :
    phdr.p_vaddr.toNat + phdr.p_memsz.toNat + (segmentLayoutAlign phdr.p_align).toNat < 2 ^ 64
  /-- General `Rela` relocations. -/
  rela   : Array (Rela phdr.p_vaddr phdr.p_memsz)
  /-- PLT relocations. -/
  jmprel : Array (Rela phdr.p_vaddr phdr.p_memsz)
  deriving Repr

namespace Segment

/-- gabi `p_vaddr` — ELF address in process memory. -/
@[simp] def eaddr (s : Segment) : Eaddr := s.phdr.p_vaddr

/-- gabi `p_memsz` — total memory size in process. -/
@[simp] def memsz (s : Segment) : ByteSize := s.phdr.p_memsz

/-- gabi `p_filesz` — file-backed size; `[filesz, memsz)` is BSS. -/
@[simp] def filesz (s : Segment) : ByteSize := s.phdr.p_filesz

/-- gabi `p_offset` — file offset of segment's bytes. -/
@[simp] def offset (s : Segment) : FileOff := s.phdr.p_offset

/-- gabi `p_flags`, already decoded to named RWX bits. -/
def perm (s : Segment) : ProgramHeaderFlags := s.phdr.p_flags

/-- gabi `p_align`. -/
@[simp] def align (s : Segment) : UInt64 := s.phdr.p_align

/-- The segment memory image contains the half-open ELF-address range
    `[addr, addr + len)`. -/
def ContainsEaddrRange (s : Segment) (addr : Eaddr) (len : ByteSize) : Prop :=
  s.eaddr.toNat ≤ addr.toNat ∧
  addr.toNat + len.toNat ≤ s.eaddr.toNat + s.memsz.toNat

instance (s : Segment) (addr : Eaddr) (len : ByteSize) :
    Decidable (ContainsEaddrRange s addr len) := by
  unfold ContainsEaddrRange; infer_instance

/-- The segment memory image contains this ELF address. -/
def ContainsEaddr (s : Segment) (addr : Eaddr) : Prop :=
  s.eaddr.toNat ≤ addr.toNat ∧
  addr.toNat < s.eaddr.toNat + s.memsz.toNat

instance (s : Segment) (addr : Eaddr) :
    Decidable (ContainsEaddr s addr) := by
  unfold ContainsEaddr; infer_instance

/-- The segment's file-backed image contains the half-open file range
    `[off, off + len)`. -/
def ContainsFileRange (s : Segment) (off : FileOff) (len : ByteSize) : Prop :=
  s.offset.toNat ≤ off.toNat ∧
  off.toNat + len.toNat ≤ s.offset.toNat + s.filesz.toNat

instance (s : Segment) (off : FileOff) (len : ByteSize) :
    Decidable (ContainsFileRange s off len) := by
  unfold ContainsFileRange; infer_instance

/-- The segment's file-backed image contains the half-open ELF-address range
    `[addr, addr + len)`. Dynamic pointers must satisfy this stronger property:
    reading bytes from a BSS-only part of `p_memsz` is invalid. -/
def ContainsFileBackedEaddrRange (s : Segment) (addr : Eaddr) (len : ByteSize) : Prop :=
  s.eaddr.toNat ≤ addr.toNat ∧
  addr.toNat + len.toNat ≤ s.eaddr.toNat + s.filesz.toNat

instance (s : Segment) (addr : Eaddr) (len : ByteSize) :
    Decidable (ContainsFileBackedEaddrRange s addr len) := by
  unfold ContainsFileBackedEaddrRange; infer_instance

/-- File offset corresponding to a ELF address inside the segment's
    file-backed image. The `ContainsFileBackedEaddrRange` witness is carried by
    callers that need this formula to be semantically valid. -/
def fileOffOfEaddr (s : Segment) (addr : Eaddr) : FileOff :=
  ⟨s.offset.val + (addr.val - s.eaddr.val)⟩

/-- ELF address corresponding to a file offset inside the segment's
    file-backed image. Callers carry the file-backed containment witness that
    makes this translation meaningful. -/
def eaddrOfFileOff (s : Segment) (off : FileOff) : Eaddr :=
  ⟨s.eaddr.val + (off.val - s.offset.val)⟩

/-- Keep a checked segment's established byte-layout witnesses while attaching
    the relocations that parse located inside its memory range. -/
def withRelocs (s : Segment)
    (rela jmprel : Array (Rela s.phdr.p_vaddr s.phdr.p_memsz)) : Segment :=
  { s with rela, jmprel }

end Segment

-- ============================================================================
-- Smart constructor.
-- ============================================================================

/-- Lift a decidable proposition into `Except` (with `PLift` to bridge
    `Prop` through `Except`'s `Type` parameter). -/
private def assertProp (p : Prop) [Decidable p] (msg : String) :
    Except String (PLift p) :=
  if h : p then .ok ⟨h⟩ else .error msg

/-- Smart constructor: build a `Segment` from a `ProgramHeader` and pre-located rela
    arrays. Decidably checks each gabi-07 per-segment invariant plus the
    memory/file/page-layout no-wrap witnesses, failing with a typed error. -/
def Segment.ofPhdr (phdr : ProgramHeader) (fileSize : UInt64)
    (rela jmprel : Array (Rela phdr.p_vaddr phdr.p_memsz)) :
    Except String Segment := do
  let ⟨isLoad⟩ ← assertProp (phdr.p_type = .load)
    s!"p_type={reprStr phdr.p_type} is not PT_LOAD"
  let ⟨memNoWrap⟩ ← assertProp
    (phdr.p_vaddr.toNat + phdr.p_memsz.toNat < 2 ^ 64)
    s!"p_vaddr+p_memsz wraps UInt64 \
       (0x{phdr.p_vaddr.toNat}+0x{phdr.p_memsz.toNat})"
  let ⟨fileInBounds⟩ ← assertProp
    (phdr.p_offset.toNat + phdr.p_filesz.toNat ≤ fileSize.toNat)
    s!"p_offset+p_filesz is past file size \
       (0x{phdr.p_offset.toNat}+0x{phdr.p_filesz.toNat} > 0x{fileSize.toNat})"
  let ⟨fileszLeMemsz⟩ ← assertProp (phdr.p_filesz.toNat ≤ phdr.p_memsz.toNat)
    s!"p_filesz=0x{phdr.p_filesz.toNat} > p_memsz=0x{phdr.p_memsz.toNat} \
       (gabi-07 § Program Header)"
  let ⟨alignPow2⟩ ← assertProp
    (phdr.p_align = 0 ∨ (phdr.p_align &&& (phdr.p_align - 1)) = 0)
    s!"p_align=0x{phdr.p_align.toNat} is not a power of 2 \
       (gabi-07 § Program Header)"
  let ⟨alignCong⟩ ← assertProp
    (phdr.p_align = 0 ∨ phdr.p_vaddr.val % phdr.p_align = phdr.p_offset.val % phdr.p_align)
    "alignment congruence violated (gabi-07: p_vaddr ≡ p_offset mod p_align)"
  let ⟨pageLayoutNoWrap⟩ ← assertProp
    (phdr.p_vaddr.toNat + phdr.p_memsz.toNat +
      (segmentLayoutAlign phdr.p_align).toNat < 2 ^ 64)
    s!"p_vaddr+p_memsz+effective_align wraps UInt64 \
       (0x{phdr.p_vaddr.toNat}+0x{phdr.p_memsz.toNat}+\
       0x{(segmentLayoutAlign phdr.p_align).toNat})"
  return {
    fileSize, phdr, isLoad,
    eaddrRange := { noWrap := memNoWrap },
    fileRange := { inFile := fileInBounds },
    fileszLeMemsz, alignPow2, alignCong, pageLayoutNoWrap, rela, jmprel
  }

end LeanLoad.Parse

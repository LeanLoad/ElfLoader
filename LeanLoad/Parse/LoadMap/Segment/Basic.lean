/-
Checked PT_LOAD segment — gabi-07 byte fields and per-segment invariants.

Spec: gabi 07 (`third_party/gabi/docsrc/elf/07-pheader.rst`) § Program
Header.

Carried as struct fields:
  - the originating `ProgramHeader` fields, via `extends`, plus a witness that
    it is `PT_LOAD`,
  - the `PT_LOAD`-specific gabi-07 invariant (`fileszLeMemsz`),
  - typed memory witnesses and the page-layout no-wrap bound that let
    `Layout.SegmentLayout` ignore UInt64 wrap without a platform-sized
    address-space shortcut. File-image bounds, memory-image no-wrap, and
    alignment invariants live on `ProgramHeader`.

This file is *gabi-only*. mmap semantics (page-aligned addresses, BSS bounds,
POSIX `PROT_*`) live on `Layout.SegmentLayout`, which couples a segment with its
chosen mmap base.
-/

import LeanLoad.Parse.LoadMap.ProgramHeader.Basic
import LeanLoad.Parse.Basic

namespace LeanLoad.Parse

private def u64Limit : Nat := 2 ^ 64

-- ============================================================================
-- Segment — gabi-07 byte fields + invariants. mmap-stage semantics
-- live on `Layout.SegmentLayout`.
-- ============================================================================

/-- A PT_LOAD segment: a checked program-header row plus PT_LOAD-specific
    invariants and layout no-wrap witnesses. -/
structure Segment (fileSize : ByteSize) extends ProgramHeader fileSize where
  /-- This checked segment is backed by a `PT_LOAD` phdr. -/
  isLoad : p_type = .load
  /-- gabi 07: `p_filesz ≤ p_memsz`. -/
  fileszLeMemsz : p_filesz.toNat ≤ p_memsz.toNat
  /-- No UInt64 wrap when page layout rounds `[p_vaddr, p_vaddr + p_memsz)`
      by the effective alignment used by `Layout.SegmentLayout`. This is a
      loader arithmetic bound, not a 48-bit platform policy. -/
  pageLayoutNoWrap :
    p_vaddr.toNat + p_memsz.toNat + (segmentLayoutAlign p_align).toNat < u64Limit
  deriving Repr

namespace Segment

/-- gabi `p_vaddr` — ELF address in process memory. -/
@[simp] def eaddr {fileSize : ByteSize} (s : Segment fileSize) : Eaddr := s.p_vaddr

/-- gabi `p_memsz` — total memory size in process. -/
@[simp] def memsz {fileSize : ByteSize} (s : Segment fileSize) : ByteSize := s.p_memsz

/-- gabi `p_filesz` — file-backed size; `[filesz, memsz)` is BSS. -/
@[simp] def filesz {fileSize : ByteSize} (s : Segment fileSize) : ByteSize := s.p_filesz

/-- gabi `p_offset` — file offset of segment's bytes. -/
@[simp] def offset {fileSize : ByteSize} (s : Segment fileSize) : FileOff := s.p_offset

/-- gabi `p_flags`, already decoded to named RWX bits. -/
def perm {fileSize : ByteSize} (s : Segment fileSize) : ProgramHeaderFlags := s.p_flags

/-- gabi `p_align`. -/
@[simp] def align {fileSize : ByteSize} (s : Segment fileSize) : UInt64 := s.p_align

/-- The segment memory image contains the half-open ELF-address range
    `[addr, addr + len)`. -/
def ContainsEaddrRange {fileSize : ByteSize} (s : Segment fileSize) (addr : Eaddr)
    (len : ByteSize) : Prop :=
  s.eaddr.toNat ≤ addr.toNat ∧
  addr.toNat + len.toNat ≤ s.eaddr.toNat + s.memsz.toNat

instance {fileSize : ByteSize} (s : Segment fileSize) (addr : Eaddr) (len : ByteSize) :
    Decidable (ContainsEaddrRange s addr len) := by
  unfold ContainsEaddrRange; infer_instance

/-- The segment memory image contains this ELF address. -/
def ContainsEaddr {fileSize : ByteSize} (s : Segment fileSize) (addr : Eaddr) : Prop :=
  s.eaddr.toNat ≤ addr.toNat ∧
  addr.toNat < s.eaddr.toNat + s.memsz.toNat

instance {fileSize : ByteSize} (s : Segment fileSize) (addr : Eaddr) :
    Decidable (ContainsEaddr s addr) := by
  unfold ContainsEaddr; infer_instance

/-- The segment's file-backed image contains the half-open file range
    `[off, off + len)`. -/
def ContainsFileRange {fileSize : ByteSize} (s : Segment fileSize) (off : FileOff)
    (len : ByteSize) : Prop :=
  s.offset.toNat ≤ off.toNat ∧
  off.toNat + len.toNat ≤ s.offset.toNat + s.filesz.toNat

instance {fileSize : ByteSize} (s : Segment fileSize) (off : FileOff) (len : ByteSize) :
    Decidable (ContainsFileRange s off len) := by
  unfold ContainsFileRange; infer_instance

/-- The segment's file-backed image contains the half-open ELF-address range
    `[addr, addr + len)`. Dynamic pointers must satisfy this stronger property:
    reading bytes from a BSS-only part of `p_memsz` is invalid. -/
def ContainsFileBackedEaddrRange {fileSize : ByteSize} (s : Segment fileSize) (addr : Eaddr)
    (len : ByteSize) : Prop :=
  s.eaddr.toNat ≤ addr.toNat ∧
  addr.toNat + len.toNat ≤ s.eaddr.toNat + s.filesz.toNat

instance {fileSize : ByteSize} (s : Segment fileSize) (addr : Eaddr) (len : ByteSize) :
    Decidable (ContainsFileBackedEaddrRange s addr len) := by
  unfold ContainsFileBackedEaddrRange; infer_instance

/-- File offset corresponding to a ELF address inside the segment's
    file-backed image. The `ContainsFileBackedEaddrRange` witness is carried by
    callers that need this formula to be semantically valid. -/
def fileOffOfEaddr {fileSize : ByteSize} (s : Segment fileSize) (addr : Eaddr) : FileOff :=
  ⟨s.offset.val + (addr.val - s.eaddr.val)⟩

/-- ELF address corresponding to a file offset inside the segment's
    file-backed image. Callers carry the file-backed containment witness that
    makes this translation meaningful. -/
def eaddrOfFileOff {fileSize : ByteSize} (s : Segment fileSize) (off : FileOff) : Eaddr :=
  ⟨s.eaddr.val + (off.val - s.offset.val)⟩

end Segment

-- ============================================================================
-- Smart constructor.
-- ============================================================================

/-- Smart constructor: build a `Segment` from a `ProgramHeader`. Decidably
    checks each gabi-07 per-segment invariant plus the memory/page-layout
    no-wrap witnesses, failing with a typed error. -/
def Segment.ofPhdr {fileSize : ByteSize} (phdr : ProgramHeader fileSize) :
    Except String (Segment fileSize) := do
  let vaddr := phdr.p_vaddr.toNat
  let memsz := phdr.p_memsz.toNat
  let align := phdr.p_align
  let effectiveAlign := segmentLayoutAlign align

  let ⟨isLoad⟩ ← require (phdr.p_type = .load)
    s!"p_type={reprStr phdr.p_type} is not PT_LOAD"
  let ⟨fileszLeMemsz⟩ ← require (phdr.p_filesz.toNat ≤ memsz)
    s!"p_filesz=0x{phdr.p_filesz.toNat} > p_memsz=0x{memsz} \
       (gabi-07 § Program Header)"
  let ⟨pageLayoutNoWrap⟩ ← require
    (vaddr + memsz + effectiveAlign.toNat < u64Limit)
    s!"p_vaddr+p_memsz+effective_align wraps UInt64 \
       (0x{vaddr}+0x{memsz}+0x{effectiveAlign.toNat})"
  return {
    toProgramHeader := phdr,
    isLoad,
    fileszLeMemsz,
    pageLayoutNoWrap
  }

end LeanLoad.Parse

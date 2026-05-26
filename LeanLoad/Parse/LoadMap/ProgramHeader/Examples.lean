/-
Examples and fixture bytes for program-header parsing and `AT_PHDR` mapping.
-/

import LeanLoad.Parse.LoadMap.ProgramHeader.Map

namespace LeanLoad.Parse.Examples

/-- 112-byte program-header fixture: one PT_LOAD covering the full 520-byte file
    at `eaddr = offset = 0` (the normal linker shape, though checked parse can
    translate non-identity `p_offset`/`p_vaddr` pairs), plus one PT_DYNAMIC
    pointing at the dynamic section at offset 0x128. Coordinated with
    `Parse.Examples.fixtureMainBytes`. -/
def programHeaderBytes : ByteArray := ⟨#[
  -- ProgramHeader[0]: PT_LOAD covering [0..0x208] ────────────────────────────────
  0x01, 0x00, 0x00, 0x00,                           -- p_type   = PT_LOAD
  0x05, 0x00, 0x00, 0x00,                           -- p_flags  = R|X = 5
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_offset = 0
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_vaddr  = 0
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_paddr  = 0
  0x08, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_filesz = 0x208
  0x08, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_memsz  = 0x208
  0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_align  = 0x1000
  -- ProgramHeader[1]: PT_DYNAMIC ─────────────────────────────────────────────────
  0x02, 0x00, 0x00, 0x00,                           -- p_type   = PT_DYNAMIC
  0x06, 0x00, 0x00, 0x00,                           -- p_flags  = R|W = 6
  0x28, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_offset = 0x128
  0x28, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_vaddr  = 0x128
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_paddr  = 0
  0xe0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_filesz = 0xe0
  0xe0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_memsz  = 0xe0
  0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00    -- p_align  = 8
]⟩

#guard programHeaderBytes.size == 2 * ProgramHeaderSize  -- = 112

def rawProgramHeaders? : Option (Array RawProgramHeader) :=
  (Decodable.decodeArray (α := RawProgramHeader) programHeaderBytes 2).toOption

#guard rawProgramHeaders?.isSome

def programHeaderFileSize : ByteSize := 0x208

def programHeaders? : Option (Array (ProgramHeader programHeaderFileSize)) :=
  (ProgramHeader.arrayDecoder programHeaderFileSize 2).decode? programHeaderBytes

#guard programHeaders?.isSome

def programHeaders : Array (ProgramHeader programHeaderFileSize) :=
  programHeaders?.get (by native_decide)

#guard programHeaders.size = 2

def loadProgramHeader : ProgramHeader programHeaderFileSize := (programHeaders[0]?).getD default
def dynamicProgramHeader : ProgramHeader programHeaderFileSize := (programHeaders[1]?).getD default

-- PT_LOAD
#guard loadProgramHeader.p_type   = .load
#guard loadProgramHeader.p_flags  = ProgramHeaderFlags.ofRaw 5 -- R|X
#guard loadProgramHeader.p_vaddr  = 0
#guard loadProgramHeader.p_filesz = 0x208
#guard loadProgramHeader.p_align  = 0x1000
-- PT_DYNAMIC
#guard dynamicProgramHeader.p_type   = .dynamic
#guard dynamicProgramHeader.p_offset = 0x128
#guard dynamicProgramHeader.p_filesz = 0xe0
#guard dynamicProgramHeader.fileRange.off = 0x128
#guard dynamicProgramHeader.fileRange.size = 0xe0
#guard (ProgramHeader.arrayDecoder 0x207 2).decode? programHeaderBytes |>.isNone

-- ── Error cases ──────────────────────────────────────────────────────
-- Truncated phdr: 20 bytes when 56 (ProgramHeaderSize) expected. EOF hits
-- inside the `p_offset` u64 read.
#guard
  (ProgramHeader.decoder programHeaderFileSize).decode?
    (programHeaderBytes.extract 0 20) |>.isNone

-- `Decoder.array` asking for 3 entries from a 2-entry buffer: third
-- entry hits EOF.
#guard
  (ProgramHeader.arrayDecoder programHeaderFileSize 3).decode? programHeaderBytes |>.isNone

-- ── Checked AT_PHDR mapping ────────────────────────────────────────────────

private def mapExampleFileSize : ByteSize := 0x4000

private def mapExecProgramHeader : ProgramHeader mapExampleFileSize :=
  { (default : ProgramHeader mapExampleFileSize) with
    p_type := .load,
    p_flags := ProgramHeaderFlags.ofRaw 0x5, -- R|X
    p_offset := 0,
    p_vaddr := 0,
    p_filesz := 0x200,
    p_memsz := 0x200,
    p_align := 0x1000,
    fileInBounds := by decide,
    eaddrNoWrap := by decide,
    alignPow2 := by decide,
    alignCong := by decide }

private def mapDataProgramHeader : ProgramHeader mapExampleFileSize :=
  { (default : ProgramHeader mapExampleFileSize) with
    p_type := .load,
    p_flags := ProgramHeaderFlags.ofRaw 0x6, -- R|W
    p_offset := 0x1000,
    p_vaddr := 0x1000,
    p_filesz := 0x100,
    p_memsz := 0x200,
    p_align := 0x1000,
    fileInBounds := by decide,
    eaddrNoWrap := by decide,
    alignPow2 := by decide,
    alignCong := by decide }

private def shiftedProgramHeader : ProgramHeader mapExampleFileSize :=
  { (default : ProgramHeader mapExampleFileSize) with
    p_type := .load,
    p_flags := ProgramHeaderFlags.ofRaw 0x4, -- R
    p_offset := 0x2000,
    p_vaddr := 0x3000,
    p_filesz := 0x100,
    p_memsz := 0x100,
    p_align := 0x1000,
    fileInBounds := by decide,
    eaddrNoWrap := by decide,
    alignPow2 := by decide,
    alignCong := by decide }

private def mapSegments? : Option (SegmentTable mapExampleFileSize) :=
  match Segment.ofPhdr mapExecProgramHeader,
      Segment.ofPhdr mapDataProgramHeader with
  | .ok execSeg, .ok dataSeg =>
      match SegmentTable.ofArray #[execSeg, dataSeg] with
      | .ok segs => some segs
      | .error _ => none
  | _, _ => none

private def shiftedSegments? : Option (SegmentTable mapExampleFileSize) :=
  match Segment.ofPhdr shiftedProgramHeader with
  | .ok seg =>
      match SegmentTable.ofArray #[seg] with
      | .ok segs => some segs
      | .error _ => none
  | .error _ => none

private def programHeaderMapped? (segments : SegmentTable mapExampleFileSize) (phoff : FileOff)
    (nbytes : Nat) : Bool :=
  match ProgramHeaderMap.ofSegments segments phoff nbytes with
  | .ok _    => true
  | .error _ => false

#guard
  match mapSegments? with
  | some segs => programHeaderMapped? segs 0x40 0x80
  | none => false

#guard
  match mapSegments? with
  | some segs => !(programHeaderMapped? segs 0x3000 0x10)
  | none => false

-- `ProgramHeaderMap` requires bytes covered by `p_filesz`, not the PT_LOAD's BSS tail.
#guard
  match mapSegments? with
  | some segs => !(programHeaderMapped? segs 0x1150 0x10)
  | none => false

-- Non-identity `p_offset`/`p_vaddr` program-header coverage is accepted, and the checked
-- map records the translated ELF address used for `AT_PHDR`.
#guard
  match shiftedSegments? with
  | some segs =>
      match ProgramHeaderMap.ofSegments segs 0x2040 0x20 with
      | .ok m    => m.eaddr == 0x3040
      | .error _ => false
  | none => false

end LeanLoad.Parse.Examples

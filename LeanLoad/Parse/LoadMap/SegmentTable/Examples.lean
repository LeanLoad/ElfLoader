/-
Examples for checked PT_LOAD segments and checked segment arrays.
-/

import LeanLoad.Parse.LoadMap.SegmentTable.Basic

namespace LeanLoad.Parse.Examples

private def exampleFileSize : UInt64 := 0x4000

private def execProgramHeader : ProgramHeader :=
  { (default : ProgramHeader) with
    p_type := .load,
    p_flags := ProgramHeaderFlags.ofRaw 0x5, -- R|X
    p_offset := 0,
    p_vaddr := 0,
    p_filesz := 0x200,
    p_memsz := 0x200,
    p_align := 0x1000 }

private def dataProgramHeader : ProgramHeader :=
  { (default : ProgramHeader) with
    p_type := .load,
    p_flags := ProgramHeaderFlags.ofRaw 0x6, -- R|W
    p_offset := 0x1000,
    p_vaddr := 0x1000,
    p_filesz := 0x100,
    p_memsz := 0x200,
    p_align := 0x1000 }

private def overlapProgramHeader : ProgramHeader :=
  { (default : ProgramHeader) with
    p_type := .load,
    p_flags := ProgramHeaderFlags.ofRaw 0x4, -- R
    p_offset := 0x100,
    p_vaddr := 0x100,
    p_filesz := 0x10,
    p_memsz := 0x10,
    p_align := 0x100 }

private def shiftedProgramHeader : ProgramHeader :=
  { (default : ProgramHeader) with
    p_type := .load,
    p_flags := ProgramHeaderFlags.ofRaw 0x4, -- R
    p_offset := 0x2000,
    p_vaddr := 0x3000,
    p_filesz := 0x100,
    p_memsz := 0x100,
    p_align := 0x1000 }

private def execSeg? : Option Segment :=
  match Segment.ofPhdr execProgramHeader exampleFileSize with
  | .ok seg => some seg
  | .error _ => none

#guard
  match execSeg? with
  | some s => s.perm.read && s.perm.exec && !s.perm.write && s.eaddr == 0
  | none => false

private def checkedSegments? : Option SegmentTable :=
  match Segment.ofPhdr execProgramHeader exampleFileSize,
      Segment.ofPhdr dataProgramHeader exampleFileSize with
  | .ok execSeg, .ok dataSeg =>
      match SegmentTable.ofArray #[execSeg, dataSeg] with
      | .ok segs => some segs
      | .error _ => none
  | _, _ => none

#guard checkedSegments?.map (·.items.size) = some 2

-- `SegmentTable.ofArray` rejects unsorted PT_LOAD arrays.
#guard
  match Segment.ofPhdr execProgramHeader exampleFileSize,
      Segment.ofPhdr dataProgramHeader exampleFileSize with
  | .ok execSeg, .ok dataSeg =>
      match SegmentTable.ofArray #[dataSeg, execSeg] with
      | .error _ => true
      | .ok _ => false
  | _, _ => false

-- `SegmentTable.ofArray` rejects overlapping sorted PT_LOAD arrays.
#guard
  match Segment.ofPhdr execProgramHeader exampleFileSize,
      Segment.ofPhdr overlapProgramHeader exampleFileSize with
  | .ok execSeg, .ok overlapSeg =>
      match SegmentTable.ofArray #[execSeg, overlapSeg] with
      | .error _ => true
      | .ok _ => false
  | _, _ => false

private def shiftedSegments? : Option SegmentTable :=
  match Segment.ofPhdr shiftedProgramHeader exampleFileSize with
  | .ok seg =>
      match SegmentTable.ofArray #[seg] with
      | .ok segs => some segs
      | .error _ => none
  | .error _ => none

private def programHeaderMapped? (segments : SegmentTable) (phoff : FileOff) (nbytes : Nat) : Bool :=
  match ProgramHeaderMap.ofSegments segments phoff nbytes with
  | .ok _    => true
  | .error _ => false

#guard
  match checkedSegments? with
  | some segs => programHeaderMapped? segs 0x40 0x80
  | none => false

#guard
  match checkedSegments? with
  | some segs => !(programHeaderMapped? segs 0x3000 0x10)
  | none => false

-- `ProgramHeaderMap` requires file-backed bytes, not just BSS memory coverage.
#guard
  match checkedSegments? with
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

private def callTargetInExecSeg? (segments : SegmentTable) (entry : Eaddr) : Bool :=
  letI : Decidable (callTargetInExecSeg segments entry) := by
    unfold callTargetInExecSeg SegmentTable.ExecAddr SegmentTable.ContainsEaddr Segment.ContainsEaddr
    infer_instance
  if _ : callTargetInExecSeg segments entry then true else false

private def containsEaddrRange? (s : Segment) (addr : Eaddr) (len : ByteSize) : Bool :=
  if _ : Segment.ContainsEaddrRange s addr len then true else false

private def containsFileRange? (s : Segment) (off : FileOff) (len : ByteSize) : Bool :=
  if _ : Segment.ContainsFileRange s off len then true else false

#guard
  match checkedSegments? with
  | some segs =>
      callTargetInExecSeg? segs 0x10 &&
      callTargetInExecSeg? segs 0 &&
      !(callTargetInExecSeg? segs 0x1010)
  | none => false

#guard
  match execSeg? with
  | some s =>
      containsEaddrRange? s 0x10 0x8 &&
      containsFileRange? s 0x10 0x8 &&
      !(containsEaddrRange? s 0x1ff 0x8)
  | none => false

end LeanLoad.Parse.Examples

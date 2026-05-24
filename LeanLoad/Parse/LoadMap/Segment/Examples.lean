/-
Examples for checked PT_LOAD segments and checked segment arrays.
-/

import LeanLoad.Parse.LoadMap.Segment.Table

namespace LeanLoad.Parse.Examples

private def exampleFileSize : ByteSize := 0x4000

private def execProgramHeader : ProgramHeader exampleFileSize :=
  { (default : ProgramHeader exampleFileSize) with
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

private def dataProgramHeader : ProgramHeader exampleFileSize :=
  { (default : ProgramHeader exampleFileSize) with
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

private def overlapProgramHeader : ProgramHeader exampleFileSize :=
  { (default : ProgramHeader exampleFileSize) with
    p_type := .load,
    p_flags := ProgramHeaderFlags.ofRaw 0x4, -- R
    p_offset := 0x100,
    p_vaddr := 0x100,
    p_filesz := 0x10,
    p_memsz := 0x10,
    p_align := 0x100,
    fileInBounds := by decide,
    eaddrNoWrap := by decide,
    alignPow2 := by decide,
    alignCong := by decide }

private def execSeg? : Option (Segment exampleFileSize) :=
  match Segment.ofPhdr execProgramHeader with
  | .ok seg => some seg
  | .error _ => none

#guard
  match execSeg? with
  | some s => s.perm.read && s.perm.exec && !s.perm.write && s.eaddr == 0
  | none => false

private def checkedSegments? : Option (SegmentTable exampleFileSize) :=
  match Segment.ofPhdr execProgramHeader,
      Segment.ofPhdr dataProgramHeader with
  | .ok execSeg, .ok dataSeg =>
      match SegmentTable.ofArray #[execSeg, dataSeg] with
      | .ok segs => some segs
      | .error _ => none
  | _, _ => none

#guard checkedSegments?.map (·.items.size) = some 2

-- `SegmentTable.ofArray` rejects unsorted PT_LOAD arrays.
#guard
  match Segment.ofPhdr execProgramHeader,
      Segment.ofPhdr dataProgramHeader with
  | .ok execSeg, .ok dataSeg =>
      match SegmentTable.ofArray #[dataSeg, execSeg] with
      | .error _ => true
      | .ok _ => false
  | _, _ => false

-- `SegmentTable.ofArray` rejects overlapping sorted PT_LOAD arrays.
#guard
  match Segment.ofPhdr execProgramHeader,
      Segment.ofPhdr overlapProgramHeader with
  | .ok execSeg, .ok overlapSeg =>
      match SegmentTable.ofArray #[execSeg, overlapSeg] with
      | .error _ => true
      | .ok _ => false
  | _, _ => false

private def containsEaddrRange? (s : Segment exampleFileSize) (addr : Eaddr) (len : ByteSize) : Bool :=
  if _ : Segment.ContainsEaddrRange s addr len then true else false

private def containsFileRange? (s : Segment exampleFileSize) (off : FileOff) (len : ByteSize) : Bool :=
  if _ : Segment.ContainsFileRange s off len then true else false

#guard
  match execSeg? with
  | some s =>
      containsEaddrRange? s 0x10 0x8 &&
      containsFileRange? s 0x10 0x8 &&
      !(containsEaddrRange? s 0x1ff 0x8)
  | none => false

end LeanLoad.Parse.Examples

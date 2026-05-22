/-
Examples for checked PT_LOAD segments and checked segment arrays.
-/

import LeanLoad.Parse.Segment.Properties

namespace LeanLoad.Parse.Example

private def exampleFileSize : UInt64 := 0x4000

private def execPhdr : RawPhdr :=
  { (default : RawPhdr) with
    p_type := .load,
    p_flags := PhdrFlags.ofRaw 0x5, -- R|X
    p_offset := 0,
    p_vaddr := 0,
    p_filesz := 0x200,
    p_memsz := 0x200,
    p_align := 0x1000 }

private def dataPhdr : RawPhdr :=
  { (default : RawPhdr) with
    p_type := .load,
    p_flags := PhdrFlags.ofRaw 0x6, -- R|W
    p_offset := 0x1000,
    p_vaddr := 0x1000,
    p_filesz := 0x100,
    p_memsz := 0x200,
    p_align := 0x1000 }

private def overlapPhdr : RawPhdr :=
  { (default : RawPhdr) with
    p_type := .load,
    p_flags := PhdrFlags.ofRaw 0x4, -- R
    p_offset := 0x100,
    p_vaddr := 0x100,
    p_filesz := 0x10,
    p_memsz := 0x10,
    p_align := 0x100 }

private def execSeg? : Option Segment :=
  match Segment.ofPhdr execPhdr exampleFileSize #[] #[] with
  | .ok seg => some seg
  | .error _ => none

#guard
  match execSeg? with
  | some s => s.perm.read && s.perm.exec && !s.perm.write && s.vaddr == 0
  | none => false

private def checkedSegments? : Option Segments :=
  match Segment.ofPhdr execPhdr exampleFileSize #[] #[],
      Segment.ofPhdr dataPhdr exampleFileSize #[] #[] with
  | .ok execSeg, .ok dataSeg =>
      match Segments.ofArray #[execSeg, dataSeg] with
      | .ok segs => some segs
      | .error _ => none
  | _, _ => none

#guard checkedSegments?.map (·.items.size) = some 2

-- `Segments.ofArray` rejects unsorted PT_LOAD arrays.
#guard
  match Segment.ofPhdr execPhdr exampleFileSize #[] #[],
      Segment.ofPhdr dataPhdr exampleFileSize #[] #[] with
  | .ok execSeg, .ok dataSeg =>
      match Segments.ofArray #[dataSeg, execSeg] with
      | .error _ => true
      | .ok _ => false
  | _, _ => false

-- `Segments.ofArray` rejects overlapping sorted PT_LOAD arrays.
#guard
  match Segment.ofPhdr execPhdr exampleFileSize #[] #[],
      Segment.ofPhdr overlapPhdr exampleFileSize #[] #[] with
  | .ok execSeg, .ok overlapSeg =>
      match Segments.ofArray #[execSeg, overlapSeg] with
      | .error _ => true
      | .ok _ => false
  | _, _ => false

private def phdrCovered? (segs : Array Segment) (phoff : FileOff) (nbytes : Nat) : Bool :=
  letI : Decidable (PhdrCovered segs phoff nbytes) := by
    unfold PhdrCovered coversPhdrs
    infer_instance
  if _ : PhdrCovered segs phoff nbytes then true else false

#guard
  match checkedSegments? with
  | some segs => phdrCovered? segs.items 0x40 0x80
  | none => false

#guard
  match checkedSegments? with
  | some segs => !(phdrCovered? segs.items 0x3000 0x10)
  | none => false

private def callTargetInExecSeg? (segments : Segments) (entry : Vaddr) : Bool :=
  letI : Decidable (callTargetInExecSeg segments entry) := by
    unfold callTargetInExecSeg Segments.ExecAddr Segments.ContainsVaddr Segment.ContainsVaddr
    infer_instance
  if _ : callTargetInExecSeg segments entry then true else false

private def containsVaddrRange? (s : Segment) (addr : Vaddr) (len : ByteSize) : Bool :=
  if _ : Segment.ContainsVaddrRange s addr len then true else false

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
      containsVaddrRange? s 0x10 0x8 &&
      containsFileRange? s 0x10 0x8 &&
      !(containsVaddrRange? s 0x1ff 0x8)
  | none => false

end LeanLoad.Parse.Example

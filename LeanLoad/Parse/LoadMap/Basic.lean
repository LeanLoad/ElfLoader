/-
Checked load map used while building `Dynamic`.

Before `Dynamic` exists, the reader must still follow dynamic-table ELF
addresses to file bytes. `LoadMap` is that pre-stage capability:
header policy plus checked PT_LOAD segments, enough to turn a raw ELF-address
range into a file-backed `EaddrRange`.
-/

import LeanLoad.Parse.LoadMap.ElfHeader.Basic
import LeanLoad.Parse.LoadMap.ProgramHeader.Basic
import LeanLoad.Parse.LoadMap.SegmentTable.Basic

namespace LeanLoad.Parse

/-- Header policy plus checked PT_LOAD map available before dynamic content is
    read. The `segments` field carries the gabi-07 per-segment and array-level
    witnesses; reloc arrays are still empty at this stage and are attached later
    by `Dynamic.Reloc.RelocTable`. -/
structure LoadMap where
  header   : ElfHeader
  segments : SegmentTable
  deriving Repr

namespace LoadMap

/-- Dynamic-table ELF-address range translated through a checked PT_LOAD into a
    checked file range. The segment range must be file-backed (`p_filesz`), not
    merely memory-backed (`p_memsz`), because the decoder is about to read bytes
    from the ELF file. -/
structure FileBackedEaddrRange (view : LoadMap) (fileSize : UInt64) (range : EaddrRange) where
  segmentRange : SegmentTable.AnyFileBackedEaddrRange view.segments range.start range.size
  fileRange    :
    FileRange fileSize
      ((view.segments.items[segmentRange.index]).fileOffOfEaddr range.start)
      range.size

namespace FileBackedEaddrRange

/-- File offset obtained by translating the checked ELF-address range through
    the file-backed segment that contains it. -/
def fileOff (checked : FileBackedEaddrRange view fileSize range) : FileOff :=
  (view.segments.items[checked.segmentRange.index]).fileOffOfEaddr range.start

end FileBackedEaddrRange

/-- Validate header policy and PT_LOAD invariants before any dynamic pointer is
    followed. This pushes parse facts earlier than the final checked-ELF
    construction, so dynamic reads consume witnessed load-map state. -/
def ofHeaders (fileSize : UInt64) (header : ElfHeader) (programHeaders : Array ProgramHeader) :
    Except String LoadMap := do
  let loadable := programHeaders.filter (·.p_type == .load)
  let mut segmentsAcc : Array Segment := #[]
  for h : i in [:loadable.size] do
    let phdr := loadable[i]
    match Segment.ofPhdr phdr fileSize with
    | .ok seg  => segmentsAcc := segmentsAcc.push seg
    | .error e => .error s!"parse: segment[{i}]: {e}"
  match SegmentTable.ofArray segmentsAcc with
  | .ok segments => .ok { header, segments }
  | .error e     => .error e

/-- Resolve a dynamic ELF-address range through the checked load map and
    prove the corresponding file range is inside the observed file. -/
def mapRange (view : LoadMap) (fileSize : UInt64) (range : EaddrRange) :
    Except String (FileBackedEaddrRange view fileSize range) := Id.run do
  let va := range.start
  let len := range.size
  for h : i in [:view.segments.items.size] do
    let idx : Fin view.segments.items.size := ⟨i, h.upper⟩
    let seg := view.segments.items[idx]
    match (inferInstance : Decidable (Segment.ContainsFileBackedEaddrRange seg va len)) with
    | .isTrue h_in =>
        let segmentRange : SegmentTable.AnyFileBackedEaddrRange view.segments va len :=
          { index := idx, contains := h_in, permits := trivial }
        let off := (view.segments.items[segmentRange.index]).fileOffOfEaddr range.start
        if h_file : off.toNat + len.toNat ≤ fileSize.toNat then
          let fileRange : FileRange fileSize off len := { inFile := h_file }
          return .ok { segmentRange, fileRange }
        else
          return .error s!"parse: mapped file range 0x{off.toNat}..+{len.toNat} is past \
            file size {fileSize.toNat}"
    | .isFalse _ => pure ()
  return .error s!"parse: ELF-address range 0x{va.toNat}..+{len.toNat} is not \
    covered by any file-backed PT_LOAD"

end LoadMap

end LeanLoad.Parse

/-
Checked load map used while building `Dynamic`.

Before `Dynamic` exists, the reader must still follow dynamic-table ELF
addresses to file bytes. `LoadMap` is that pre-stage capability:
header policy plus checked PT_LOAD segments, enough to turn a raw ELF-address
range into a checked file-backed `FileRange`.
-/

import LeanLoad.Parse.LoadMap.ElfHeader.Basic
import LeanLoad.Parse.LoadMap.ProgramHeader.Basic
import LeanLoad.Parse.LoadMap.Segment.Table
import LeanLoad.Runtime

namespace LeanLoad.Parse

open Runtime

/-- Header policy plus checked PT_LOAD map available before dynamic content is
    read. The `segments` field carries the gabi-07 per-segment and array-level
    witnesses; reloc arrays are still empty at this stage and are attached later
    by `Reloc.RelocTable`. -/
structure LoadMap (fileSize : ByteSize) where
  header   : ElfHeader fileSize
  segments : SegmentTable fileSize
  deriving Repr

namespace LoadMap

/-- Dynamic-table ELF-address range translated through a checked PT_LOAD. The
    segment range must be file-backed (`p_filesz`), not merely memory-backed
    (`p_memsz`), because the decoder is about to read bytes from the ELF file. -/
structure FileBackedEaddrRange (view : LoadMap fileSize) (range : EaddrRange) where
  segmentRange : SegmentTable.FileBackedEaddrRangeIn view.segments range.start range.size

namespace FileBackedEaddrRange

/-- File offset obtained by translating the checked ELF-address range through
    the file-backed segment that contains it. -/
def fileOff (checked : FileBackedEaddrRange view range) : FileOff :=
  (view.segments.items[checked.segmentRange.index]).fileOffOfEaddr range.start

/-- Checked file range obtained by translating through the containing PT_LOAD. -/
def fileRange (checked : FileBackedEaddrRange view range) :
    Except String (FileRange fileSize) :=
  let off := checked.fileOff
  let size := range.size
  if h : off.toNat + size.toNat ≤ fileSize.toNat then
    .ok { off, size, inBounds := h }
  else
    .error s!"parse: translated ELF-address range at file offset 0x{off.toNat} \
      requested {size.toNat} bytes, past file size {fileSize.toNat}"

end FileBackedEaddrRange

/-- Validate header policy and PT_LOAD invariants before any dynamic pointer is
    followed. This pushes parse facts earlier than the final checked-ELF
    construction, so dynamic reads consume witnessed load-map state. -/
def ofHeaders (fileSize : ByteSize) (header : ElfHeader fileSize)
    (programHeaders : Array (ProgramHeader fileSize)) :
    Except String (LoadMap fileSize) := do
  let loadable := programHeaders.filter (·.p_type == .load)
  let mut segmentsAcc : Array (Segment fileSize) := #[]
  for h : i in [:loadable.size] do
    let phdr := loadable[i]
    match Segment.ofPhdr phdr with
    | .ok seg  => segmentsAcc := segmentsAcc.push seg
    | .error e => .error s!"parse: segment[{i}]: {e}"
  match SegmentTable.ofArray segmentsAcc with
  | .ok segments => .ok { header, segments }
  | .error e     => .error e

/-- Resolve a dynamic ELF-address range through the checked load map. -/
def mapRange (view : LoadMap fileSize) (range : EaddrRange) :
    Except String (FileBackedEaddrRange view range) := Id.run do
  let va := range.start
  let len := range.size
  for h : i in [:view.segments.items.size] do
    let idx : Fin view.segments.items.size := ⟨i, h.upper⟩
    let seg := view.segments.items[idx]
    match (inferInstance : Decidable (Segment.ContainsFileBackedEaddrRange seg va len)) with
    | .isTrue h_in =>
       let segmentRange : SegmentTable.FileBackedEaddrRangeIn view.segments va len :=
         { index := idx, contains := h_in }
       return .ok { segmentRange }
    | .isFalse _ => pure ()
  return .error s!"parse: ELF-address range 0x{va.toNat}..+{len.toNat} is not \
    covered by any file-backed PT_LOAD"

/-- Resolve a dynamic ELF-address range to the file byte range that backs it. -/
def fileRange (view : LoadMap fileSize) (range : EaddrRange) :
    Except String (FileRange fileSize) := do
  (← mapRange view range).fileRange

end LoadMap

end LeanLoad.Parse

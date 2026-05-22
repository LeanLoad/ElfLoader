/-
Checked file view used while building `Dynamic`.

Before `Dynamic` exists, the reader must still follow dynamic-table ELF
addresses to file bytes. `Dynamic.ImageView` is that pre-stage capability:
header policy plus checked PT_LOAD segments, enough to turn a raw ELF-address
range into a file-backed `EaddrRange`.
-/

import LeanLoad.Parse.ImageView.ElfHeader.Basic
import LeanLoad.Parse.ImageView.ProgramHeader.Basic
import LeanLoad.Parse.ImageView.Segment.Array

namespace LeanLoad.Parse

/-- Header policy plus checked PT_LOAD map available before dynamic content is
    read. The `segments` field carries the gabi-07 per-segment and array-level
    witnesses; reloc arrays are still empty at this stage and are attached later
    by `Elf.Relocs`. -/
structure ImageView where
  header   : ElfHeader
  segments : Segments
  deriving Repr

instance : Inhabited ImageView where
  default := { header := default, segments := Segments.empty }

namespace ImageView

/-- Validate ELF header policy and the fixed Elf64 record sizes that the byte
    readers use. The size checks come from gabi 02 § ELF Header (`Elf64_Ehdr`)
    and gabi 07 § Program Header (`Elf64_Phdr`). -/
def checkHeader (header : ElfHeader) : Except String Unit := do
  if header.ei_class != .class64 then
    .error s!"parse: only ELFCLASS64 supported \
      (got ei_class={reprStr header.ei_class})"
  if header.ei_data != .lsb then
    .error s!"parse: only little-endian supported \
      (got ei_data={reprStr header.ei_data})"
  if header.e_ehsize.toNat != ElfHeaderSize then
    .error s!"parse: e_ehsize={header.e_ehsize} but Elf64_Ehdr is {ElfHeaderSize} bytes \
      (gabi-02 § ELF Header)"
  if header.e_phentsize.toNat != ProgramHeaderSize then
    .error s!"parse: e_phentsize={header.e_phentsize} but Elf64_Phdr is {ProgramHeaderSize} bytes \
      (gabi-07 § Program Header)"
  if header.e_type == .exec then
    .error s!"parse: ET_EXEC not supported — LeanLoad expects PIE \
      (ET_DYN) inputs only. Recompile with -fPIE -pie."
  return ()

/-- Dynamic-table ELF-address range translated through a checked PT_LOAD into a
    checked file range. The segment range must be file-backed (`p_filesz`), not
    merely memory-backed (`p_memsz`), because the parser is about to read bytes
    from the ELF file. -/
structure FileBackedEaddrRange (view : ImageView) (fileSize : UInt64) (range : EaddrRange) where
  segmentRange : Segments.AnyFileBackedEaddrRange view.segments range.start range.size
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
def ofHeaders (fileSize : UInt64) (header : ElfHeader) (phdrs : Array ProgramHeader) :
    Except String ImageView := do
  checkHeader header
  let loadable := phdrs.filter (·.p_type == .load)
  let mut segmentsAcc : Array Segment := #[]
  for h : i in [:loadable.size] do
    let phdr := loadable[i]
    match Segment.ofPhdr phdr fileSize #[] #[] with
    | .ok seg  => segmentsAcc := segmentsAcc.push seg
    | .error e => .error s!"parse: segment[{i}]: {e}"
  match Segments.ofArray segmentsAcc with
  | .ok segments => .ok { header, segments }
  | .error e     => .error e

/-- Resolve a dynamic ELF-address range through the checked file view and
    prove the corresponding file range is inside the observed file. -/
def mapRange (view : ImageView) (fileSize : UInt64) (range : EaddrRange) :
    Except String (FileBackedEaddrRange view fileSize range) := Id.run do
  let va := range.start
  let len := range.size
  for h : i in [:view.segments.items.size] do
    let idx : Fin view.segments.items.size := ⟨i, h.upper⟩
    let seg := view.segments.items[idx]
    match (inferInstance : Decidable (Segment.ContainsFileBackedEaddrRange seg va len)) with
    | .isTrue h_in =>
        let segmentRange : Segments.AnyFileBackedEaddrRange view.segments va len :=
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

end ImageView

end LeanLoad.Parse

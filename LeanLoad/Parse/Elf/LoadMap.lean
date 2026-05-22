/-
Early checked PT_LOAD map for byte reads.

`RawImage` needs to follow dynamic-table virtual addresses before the final
checked `Elf` exists. This module establishes the header policy and PT_LOAD
well-formedness immediately after reading `Ehdr + phdrs`, then all dynamic
content reads go through `LoadMap.mapVaddr`.
-/

import LeanLoad.Parse.Ehdr.Basic
import LeanLoad.Parse.Phdr.Basic
import LeanLoad.Parse.Segment.Array

namespace LeanLoad.Parse.Elf

open LeanLoad.Parse

/-- Header policy plus checked PT_LOAD map available before dynamic content is
    read. The `segments` field carries the gabi-07 per-segment and array-level
    witnesses; reloc arrays are still empty at this stage and are attached later
    by `Elf.Relocs`. -/
structure LoadMap where
  header   : Ehdr
  segments : Segments
  deriving Repr

instance : Inhabited LoadMap where
  default := { header := default, segments := Segments.empty }

namespace LoadMap

/-- Validate ELF header policy and the fixed Elf64 record sizes that the byte
    readers use. The size checks come from gabi 02 § ELF Header (`Elf64_Ehdr`)
    and gabi 07 § Program Header (`Elf64_Phdr`). -/
def checkHeader (header : Ehdr) : Except String Unit := do
  if header.ei_class != .class64 then
    .error s!"parse: only ELFCLASS64 supported \
      (got ei_class={reprStr header.ei_class})"
  if header.ei_data != .lsb then
    .error s!"parse: only little-endian supported \
      (got ei_data={reprStr header.ei_data})"
  if header.e_ehsize.toNat != EhdrSize then
    .error s!"parse: e_ehsize={header.e_ehsize} but Elf64_Ehdr is {EhdrSize} bytes \
      (gabi-02 § ELF Header)"
  if header.e_phentsize.toNat != PhdrSize then
    .error s!"parse: e_phentsize={header.e_phentsize} but Elf64_Phdr is {PhdrSize} bytes \
      (gabi-07 § Program Header)"
  if header.e_type == .exec then
    .error s!"parse: ET_EXEC not supported — LeanLoad expects PIE \
      (ET_DYN) inputs only. Recompile with -fPIE -pie."
  return ()

/-- Translate a dynamic-table virtual-address range through a checked PT_LOAD.
    The range must be file-backed (`p_filesz`), not merely memory-backed
    (`p_memsz`), because the parser is about to read bytes from the ELF file. -/
structure MappedVaddr (map : LoadMap) (va : Vaddr) (len : ByteSize) where
  range    : Segments.AnyFileBackedVaddrRange map.segments va len
  off      : FileOff
  off_eq   : off = (map.segments.items[range.index]).fileOffOfVaddr va
  deriving Repr

/-- Validate header policy and PT_LOAD invariants before any dynamic pointer is
    followed. This pushes parse facts earlier than the final checked-ELF
    construction, so dynamic reads consume witnessed load-map state. -/
def ofHeaders (fileSize : UInt64) (header : Ehdr) (phdrs : Array Phdr) :
    Except String LoadMap := do
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

/-- Resolve a dynamic pointer through the checked load map. -/
def mapVaddr (map : LoadMap) (va : Vaddr) (len : ByteSize) :
    Except String (MappedVaddr map va len) := Id.run do
  for h : i in [:map.segments.items.size] do
    let idx : Fin map.segments.items.size := ⟨i, h.upper⟩
    let seg := map.segments.items[idx]
    match (inferInstance : Decidable (Segment.ContainsFileBackedVaddrRange seg va len)) with
    | .isTrue h_in =>
        let range : Segments.AnyFileBackedVaddrRange map.segments va len :=
          { index := idx, contains := h_in, permits := trivial }
        return .ok { range, off := seg.fileOffOfVaddr va, off_eq := rfl }
    | .isFalse _ => pure ()
  return .error s!"parse: virtual range 0x{va.toNat}..+{len.toNat} is not \
    covered by any file-backed PT_LOAD"

/-- Resolve a dynamic virtual-address span through the checked load map. -/
def mapSpan (map : LoadMap) (span : VaddrSpan) :
    Except String (MappedVaddr map span.start span.size) :=
  mapVaddr map span.start span.size

end LoadMap

end LeanLoad.Parse.Elf

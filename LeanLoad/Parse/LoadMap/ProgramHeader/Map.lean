/-
Checked mapping of the ELF program-header table through PT_LOAD segments.

When the runtime emits `AT_PHDR`, the table must be backed by file bytes in a
PT_LOAD segment. The resulting ELF address is computed by translating `e_phoff`
through that segment, not by assuming `p_vaddr = p_offset`.
-/

import LeanLoad.Parse.LoadMap.Segment.Table

namespace LeanLoad.Parse

namespace ProgramHeaderMap

/-- The PT_LOAD segment `s` file-backs the program-header table at file offset
    `phoff` of byte length `nbytes` (gabi 04 § ELF Header, `e_phoff`/`e_phnum`;
    gabi 07 § Program Header, `p_offset`/`p_filesz`). -/
def Covers {fileSize : ByteSize} (s : Segment fileSize) (phoff : FileOff)
    (nbytes : Nat) : Prop :=
  s.offset.toNat ≤ phoff.toNat ∧
  phoff.toNat + nbytes ≤ s.offset.toNat + s.filesz.toNat

end ProgramHeaderMap

/-- Checked program-header table mapping for `AT_PHDR`. This carries the segment index
    needed to translate the table's file offset into its loaded ELF address. -/
inductive ProgramHeaderMap {fileSize : ByteSize} (segments : SegmentTable fileSize)
    (phoff : FileOff) (nbytes : Nat) where
  | empty (isEmpty : nbytes = 0)
  | mapped (index : Fin segments.items.size)
      (covers : ProgramHeaderMap.Covers segments.items[index] phoff nbytes)
  deriving Repr

namespace ProgramHeaderMap

/-- Virtual address of the program-header table in the loaded image, relative to
    the object's base. For `phnum = 0`, `AT_PHDR` is unused and this returns 0. -/
def eaddr {fileSize : ByteSize} {segments : SegmentTable fileSize} {phoff : FileOff} {nbytes : Nat}
    (m : ProgramHeaderMap segments phoff nbytes) : Eaddr :=
  match m with
  | .empty _ => 0
  | .mapped index _ => segments.items[index].eaddrOfFileOff phoff

/-- Build a checked program-header table mapping by searching the checked PT_LOAD array. -/
def ofSegments {fileSize : ByteSize} (segments : SegmentTable fileSize) (phoff : FileOff) (nbytes : Nat) :
    Except String (ProgramHeaderMap segments phoff nbytes) := Id.run do
  if h_empty : nbytes = 0 then
    return .ok (.empty h_empty)
  for h : i in [:segments.items.size] do
    let index : Fin segments.items.size := ⟨i, h.upper⟩
    let decCovers : Decidable (Covers segments.items[index] phoff nbytes) := by
      unfold Covers
      infer_instance
    match decCovers with
    | .isTrue h_covers => return .ok (.mapped index h_covers)
    | .isFalse _ => pure ()
  return .error s!"phdr table at file offset \
    0x{phoff.toNat} (size {nbytes}) is not file-backed by any PT_LOAD; \
    AT_PHDR cannot be computed"

end ProgramHeaderMap

end LeanLoad.Parse

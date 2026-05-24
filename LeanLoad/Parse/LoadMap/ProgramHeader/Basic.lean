/-
gabi 07 § Program Header — `Elf64_Phdr` entry.

The semantic `p_type` and `p_flags` field types live in
`Parse/LoadMap/ProgramHeader/Fields.lean`; this file owns the concrete struct layout.
Checked ELF-address translation lives in `Parse/LoadMap/Basic.lean`.
-/

import LeanLoad.Parse.Decode.Decodable
import LeanLoad.Parse.Decode.Deriving
import LeanLoad.Parse.LoadMap.ProgramHeader.Fields
import LeanLoad.Parse.Address

namespace LeanLoad.Parse

/-- 64-bit program header entry. Field layout matches `Elf64_Phdr`. -/
structure ProgramHeader where
  p_type   : ProgramHeaderType
  p_flags  : ProgramHeaderFlags
  p_offset : FileOff
  p_vaddr  : Eaddr
  p_paddr  : UInt64
  p_filesz : ByteSize
  p_memsz  : ByteSize
  p_align  : UInt64
  deriving Repr, Inhabited, Decodable

/-- Size of one `Elf64_Phdr` on disk: 4+4+8*6 = 56. -/
def ProgramHeaderSize : Nat := 56

namespace ProgramHeader

/-- Byte extent of a `count`-entry program-header table. -/
def tableByteSize (count : Nat) : ByteSize :=
  ByteSize.ofEntries count ProgramHeaderSize

/-- File range occupied by a `count`-entry program-header table. -/
def tableRange (fileSize : UInt64) (off : FileOff) (count : Nat) :
    Except String (FileRange fileSize off (tableByteSize count)) :=
  let len := tableByteSize count
  if h : off.toNat + len.toNat ≤ fileSize.toNat then
    .ok { inFile := h }
  else
    .error s!"read at file offset 0x{off.toNat} requested {len.toNat} bytes, \
      past file size {fileSize.toNat}"

/-- File range occupied by the contents of this program header. -/
def fileRange (fileSize : UInt64) (phdr : ProgramHeader) :
    Except String (FileRange fileSize phdr.p_offset phdr.p_filesz) :=
  if h : phdr.p_offset.toNat + phdr.p_filesz.toNat ≤ fileSize.toNat then
    .ok { inFile := h }
  else
    .error s!"read at file offset 0x{phdr.p_offset.toNat} requested {phdr.p_filesz.toNat} bytes, \
      past file size {fileSize.toNat}"

/-- Decode `count` consecutive program-header entries from the current cursor. -/
def decodeTable (count : Nat) : Decoder (Array ProgramHeader) :=
  Decoder.array count (Decodable.decoder (α := ProgramHeader))

end ProgramHeader

end LeanLoad.Parse

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

#guard Decodable.byteSize (α := ProgramHeader) = ProgramHeaderSize

/-- Byte extent of a `count`-entry program-header table. -/
def tableByteSize (count : Nat) : ByteSize :=
  ByteSize.ofEntries count (Decodable.byteSize (α := ProgramHeader))

end ProgramHeader

end LeanLoad.Parse

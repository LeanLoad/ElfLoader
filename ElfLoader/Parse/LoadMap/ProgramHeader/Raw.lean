/-
gabi 07 § Program Header — raw `Elf64_Phdr` entry.

The semantic `p_type` and `p_flags` field types live in
`Parse/LoadMap/ProgramHeader/Fields.lean`; this file owns the concrete byte
layout.
-/

import ElfLoader.Parse.Decode.Decodable
import ElfLoader.Parse.Decode.Deriving
import ElfLoader.Parse.LoadMap.ProgramHeader.Fields
import ElfLoader.Parse.Basic

namespace ElfLoader.Parse

/-- 64-bit program header entry decoded directly from bytes. Field layout matches
    `Elf64_Phdr`; file-size-dependent range witnesses are attached by
    `ProgramHeader fileSize`. -/
structure RawProgramHeader where
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

namespace RawProgramHeader

#guard (Decodable.byteSize (α := RawProgramHeader)).toNat = ProgramHeaderSize

end RawProgramHeader

end ElfLoader.Parse

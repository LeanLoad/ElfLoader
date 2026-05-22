/-
gabi 07 § Program Header — `Elf64_Phdr` entry.

The semantic `p_type` and `p_flags` field types live in
`Parse/ImageView/ProgramHeader/Fields.lean`; this file owns the concrete struct layout.
Checked ELF-address translation lives in `Parse/ImageView/Basic.lean`.
-/

import LeanLoad.Parse.Decode
import LeanLoad.Parse.Deriving
import LeanLoad.Parse.ImageView.ProgramHeader.Fields
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
  deriving Repr, Inhabited, BytesDecode

/-- Size of one `Elf64_Phdr` on disk: 4+4+8*6 = 56. -/
def ProgramHeaderSize : Nat := 56

namespace ProgramHeader

/-- Byte extent of a `count`-entry program-header table. -/
def tableByteSize (count : Nat) : ByteSize :=
  ByteSize.ofEntries count ProgramHeaderSize

/-- Parse one program-header entry from the current cursor. -/
def parse : Parser ProgramHeader :=
  BytesDecode.decode

/-- Parse `count` consecutive program-header entries from the current cursor. -/
def parseTable (count : Nat) : Parser (Array ProgramHeader) :=
  decodeArray (α := ProgramHeader) count

end ProgramHeader

end LeanLoad.Parse

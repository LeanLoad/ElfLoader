/-
gabi 07 § Program Header — `Elf64_Phdr` entry.

The semantic `p_type` and `p_flags` field types live in
`Parse/Phdr/Fields.lean`; this file owns the concrete struct layout.
Checked virtual-address translation lives in `Parse/Elf/LoadMap.lean`.
-/

import LeanLoad.Parse.Decode
import LeanLoad.Parse.Deriving
import LeanLoad.Parse.Phdr.Fields
import LeanLoad.Parse.Address

namespace LeanLoad.Parse

/-- 64-bit program header entry. Field layout matches `Elf64_Phdr`. -/
structure Phdr where
  p_type   : PhdrType
  p_flags  : PhdrFlags
  p_offset : FileOff
  p_vaddr  : Vaddr
  p_paddr  : UInt64
  p_filesz : ByteSize
  p_memsz  : ByteSize
  p_align  : UInt64
  deriving Repr, Inhabited, BytesDecode

/-- Size of one `Elf64_Phdr` on disk: 4+4+8*6 = 56. -/
def PhdrSize : Nat := 56

namespace Phdr

/-- Byte extent of a `count`-entry program-header table. -/
def tableByteSize (count : Nat) : ByteSize :=
  ByteSize.ofEntries count PhdrSize

/-- Parse one program-header entry from the current cursor. -/
def parse : Parser Phdr :=
  BytesDecode.decode

/-- Parse `count` consecutive program-header entries from the current cursor. -/
def parseTable (count : Nat) : Parser (Array Phdr) :=
  decodeArray (α := Phdr) count

end Phdr

end LeanLoad.Parse

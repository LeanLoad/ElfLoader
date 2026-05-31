/-
Examples and fixture checks for `Parse/LoadMap/ElfIdent`.
-/

import ElfLoader.Parse.LoadMap.ElfIdent.Basic

namespace ElfLoader.Parse.Examples

/-- The 16-byte `e_ident` prefix used by the consolidated ELF fixture. -/
def elfIdentBytes : ByteArray := ⟨#[
  0x7f, 0x45, 0x4c, 0x46,                           -- magic "\x7fELF"
  0x02,                                             -- EI_CLASS    = ELFCLASS64
  0x01,                                             -- EI_DATA     = ELFDATA2LSB
  0x01,                                             -- EI_VERSION
  0x00,                                             -- EI_OSABI    = System V
  0x00,                                             -- EI_ABIVERSION
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00          -- EI_PAD × 7
]⟩

#guard elfIdentBytes.size == 16

def elfIdent? : Option ElfIdent :=
  (Decodable.decode (α := ElfIdent) elfIdentBytes).toOption

#guard elfIdent?.isSome

def elfIdent : ElfIdent :=
  elfIdent?.get (by native_decide)

#guard elfIdent.magic = .elf
#guard elfIdent.ei_class = .class64
#guard elfIdent.ei_data = .lsb
#guard elfIdent.ei_version = .current
#guard elfIdent.ei_osabi = .none

def badMagicElfIdentBytes : ByteArray :=
  let bytes := elfIdentBytes.toList.toArray
  let bytes := bytes.set! 0x00 0x00
  ⟨bytes⟩

#guard (Decodable.decode (α := ElfIdent) badMagicElfIdentBytes).toOption.isNone

def badClassElfIdentBytes : ByteArray :=
  let bytes := elfIdentBytes.toList.toArray
  let bytes := bytes.set! 0x04 0xff
  ⟨bytes⟩

#guard (Decodable.decode (α := ElfIdent) badClassElfIdentBytes).toOption.isNone

def truncatedElfIdentBytes : ByteArray :=
  elfIdentBytes.extract 0 15

#guard (Decodable.decode (α := ElfIdent) truncatedElfIdentBytes).toOption.isNone

end ElfLoader.Parse.Examples

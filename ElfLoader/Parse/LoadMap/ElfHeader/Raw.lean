/-
gabi 02 § ELF Header — `Elf64_Ehdr`. Field layout matches the C
struct one-for-one, including the inlined 16-byte `e_ident` prefix
(gabi 02 § ELF Identification).

The identification fields are typed in `Parse/LoadMap/ElfIdent`; the remaining
header tag/version/sentinel fields are typed in `Parse/LoadMap/ElfHeader/Fields`.
Their decoders fold validation and sentinel decoding into byte decode, so later
stages consume semantic fields rather than raw integers.
-/

import ElfLoader.Parse.Decode.Decodable
import ElfLoader.Parse.Decode.Deriving
import ElfLoader.Parse.Basic
import ElfLoader.Parse.LoadMap.ElfIdent.Basic
import ElfLoader.Parse.LoadMap.ElfHeader.Fields
import ElfLoader.Parse.LoadMap.ProgramHeader.Raw

namespace ElfLoader.Parse

/-- Size of `Elf64_Ehdr` on disk: 16-byte e_ident + 48 bytes = 64. -/
def ElfHeaderSize : Nat := 64

/-- Fixed-width ELF header decoded directly from bytes.

    This stage knows the fixed-width byte layout and semantic scalar fields, but
    not ElfLoader policy or the containing file size. `ElfHeader fileSize` adds
    those witnesses after the runtime file size is known. -/
structure RawElfHeader where
  -- ── e_ident (16 bytes, gabi 02 § ELF Identification) ─────────────────
  ident : ElfIdent
  -- ── rest of Elf64_Ehdr (48 bytes) ────────────────────────────────────
  e_type      : ElfType
  e_machine   : ElfMachine
  e_version   : ElfVersion
  e_entry     : Eaddr
  e_phoff     : FileOff
  e_shoff     : FileOff
  e_flags     : UInt32
  e_ehsize    : UInt16
  e_phentsize : UInt16
  e_phnum     : UInt16
  e_shentsize : UInt16
  e_shnum     : UInt16
  e_shstrndx  : ElfShstrndx
  deriving Repr, Decodable

namespace RawElfHeader

#guard (Decodable.byteSize (α := RawElfHeader)).toNat = ElfHeaderSize

end RawElfHeader

end ElfLoader.Parse

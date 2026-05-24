/-
gabi 02 § ELF Header — `Elf64_Ehdr`. Field layout matches the C
struct one-for-one, including the inlined 16-byte `e_ident` prefix
(gabi 02 § ELF Identification).

The identification fields are typed in `Parse/LoadMap/ElfIdent`; the remaining
header tag/version/sentinel fields are typed in `Parse/LoadMap/ElfHeader/Fields`.
Their decoders fold validation and sentinel decoding into byte decode, so later
stages consume semantic fields rather than raw integers.
-/

import LeanLoad.Parse.Decode.Decodable
import LeanLoad.Parse.Decode.Deriving
import LeanLoad.Parse.Address
import LeanLoad.Parse.LoadMap.ElfIdent.Basic
import LeanLoad.Parse.LoadMap.ElfHeader.Fields
import LeanLoad.Parse.LoadMap.ProgramHeader.Basic

namespace LeanLoad.Parse

/-- Size of `Elf64_Ehdr` on disk: 16-byte e_ident + 48 bytes = 64. -/
def ElfHeaderSize : Nat := 64

/-- ELF header accepted by LeanLoad's load-map stage. Field layout matches
    `Elf64_Ehdr`, with LeanLoad's header policy attached as proof fields.

    The `e_ident` prefix and header tags are decoded through semantic field
    types; unknown or unsupported values fail decoding. -/
structure ElfHeader where
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
  -- ── LeanLoad-supported header properties ──────────────────────────────
  /-- LeanLoad supports only ELFCLASS64 inputs. -/
  class64     : ident.ei_class = .class64
  /-- LeanLoad targets little-endian psABIs. -/
  littleEndian : ident.ei_data = .lsb
  /-- Fixed `Elf64_Ehdr` size expected by the byte decoder. -/
  ehsizeOk    : e_ehsize.toNat = ElfHeaderSize
  /-- Fixed `Elf64_Phdr` size expected by the program-header decoder. -/
  phentsizeOk : e_phentsize.toNat = ProgramHeaderSize
  /-- LeanLoad supports PIE/shared-object style `ET_DYN`, not fixed-address `ET_EXEC`. -/
  notExec     : e_type ≠ .exec
  deriving Repr, Decodable

namespace ElfHeader

#guard Decodable.byteSize (α := ElfHeader) = ElfHeaderSize

end ElfHeader

end LeanLoad.Parse

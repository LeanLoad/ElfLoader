/-
gabi 02 § ELF Header — `Elf64_Ehdr`. Field layout matches the C
struct one-for-one, including the inlined 16-byte `e_ident` prefix
(gabi 02 § ELF Identification).

The identification fields are typed in `Parse/ImageView/ElfHeader/Ident.lean`; the
remaining header tag/version/sentinel fields are typed in
`Parse/ImageView/ElfHeader/Fields.lean`. Their decoders fold validation and sentinel
decoding into byte decode, so later stages consume semantic fields
rather than raw integers.
-/

import LeanLoad.Parse.Decode
import LeanLoad.Parse.Deriving
import LeanLoad.Parse.Address
import LeanLoad.Parse.ImageView.ElfHeader.Ident
import LeanLoad.Parse.ImageView.ElfHeader.Fields

namespace LeanLoad.Parse

/-- 64-bit ELF file header. Field layout matches `Elf64_Ehdr` —
    the 16-byte `e_ident` is inlined as the first 7 fields (gabi 02
    declares `e_ident` as an `unsigned char[EI_NIDENT]`, not as a
    named sub-struct), followed by the remaining 48 bytes.

    Magic verification happens at decode time via the `Magic` field
    type: a wrong first byte short-circuits the entire `ElfHeader`
    decode before any other field is read.

    Header tags/versions/sentinels are decoded through their semantic
    field types; unknown closed tags fail parsing. -/
structure ElfHeader where
  -- ── e_ident (16 bytes, gabi 02 § ELF Identification) ─────────────────
  magic         : Magic [0x7f, 0x45, 0x4c, 0x46]
  ei_class      : IdentClass
  ei_data       : IdentData
  ei_version    : IdentVersion
  ei_osabi      : IdentOSABI
  ei_abiversion : IdentABIVersion
  _pad          : Pad 7
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
  deriving Repr, Inhabited, BytesDecode

/-- Size of `Elf64_Ehdr` on disk: 16-byte e_ident + 48 bytes = 64. -/
def ElfHeaderSize : Nat := 64

namespace ElfHeader

/-- Byte extent of one `Elf64_Ehdr`. -/
def byteSize : ByteSize := ByteSize.ofNat ElfHeaderSize

/-- Parse one ELF header from the current cursor. -/
def parse : Parser ElfHeader :=
  BytesDecode.decode

end ElfHeader

end LeanLoad.Parse

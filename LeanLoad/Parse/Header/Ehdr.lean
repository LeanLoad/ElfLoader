/-
gabi 02 § ELF Header — `Elf64_Ehdr`. Field layout matches the C
struct one-for-one, including the inlined 16-byte `e_ident` prefix
(gabi 02 § ELF Identification).

The header tag/version/sentinel fields are typed in
`Parse/Header/Enums.lean`: `ElfClass`, `ElfData`, `ElfIdentVersion`,
`ElfOSABI`, `ElfType`, `ElfMachine`, `ElfFileVersion`, and
`EhdrShstrndx`. Their decoders fold validation and sentinel decoding
into byte decode, so later stages consume semantic fields rather than
raw integers.
-/

import LeanLoad.Parse.Decode
import LeanLoad.Parse.Deriving
import LeanLoad.Parse.Header.Enums

namespace LeanLoad.Parse

/-- 64-bit ELF file header. Field layout matches `Elf64_Ehdr` —
    the 16-byte `e_ident` is inlined as the first 7 fields (gabi 02
    declares `e_ident` as an `unsigned char[EI_NIDENT]`, not as a
    named sub-struct), followed by the remaining 48 bytes.

    Magic verification happens at decode time via the `Magic` field
    type: a wrong first byte short-circuits the entire `RawEhdr`
    decode before any other field is read.

    Header tags/versions/sentinels are decoded through their semantic
    field types; unknown closed tags fail parsing. -/
structure RawEhdr where
  -- ── e_ident (16 bytes, gabi 02 § ELF Identification) ─────────────────
  magic         : Magic [0x7f, 0x45, 0x4c, 0x46]
  ei_class      : ElfClass
  ei_data       : ElfData
  ei_version    : ElfIdentVersion
  ei_osabi      : ElfOSABI
  ei_abiversion : UInt8
  _pad          : Pad 7
  -- ── rest of Elf64_Ehdr (48 bytes) ────────────────────────────────────
  e_type      : ElfType
  e_machine   : ElfMachine
  e_version   : ElfFileVersion
  e_entry     : UInt64
  e_phoff     : UInt64
  e_shoff     : UInt64
  e_flags     : UInt32
  e_ehsize    : UInt16
  e_phentsize : UInt16
  e_phnum     : UInt16
  e_shentsize : UInt16
  e_shnum     : UInt16
  e_shstrndx  : EhdrShstrndx
  deriving Repr, Inhabited, BytesDecode

/-- Size of `Elf64_Ehdr` on disk: 16-byte e_ident + 48 bytes = 64. -/
def RawEhdrSize : Nat := 64


/-- 64-byte ELF header fixture: 64-bit, little-endian, x86-64, ET_DYN,
    with two program headers at file offset 0x40 (matching the
    `Parse.RawPhdr.fixtureBytes` layout downstream). `e_entry = 0x100`
    points inside the lone PT_LOAD of the consolidated
    `Parse.RawElf.fixtureBytes` so the elaborate-time entry-in-segment
    check passes. Section headers stripped (`e_shoff = 0`,
    `e_shnum = 0`); a loader doesn't need them. -/
def RawEhdr.fixtureBytes : ByteArray := ⟨#[
  -- e_ident (16 bytes) ──────────────────────────────────────────────────
  0x7f, 0x45, 0x4c, 0x46,                           -- magic "\x7fELF"
  0x02,                                             -- EI_CLASS    = ELFCLASS64
  0x01,                                             -- EI_DATA     = ELFDATA2LSB
  0x01,                                             -- EI_VERSION
  0x00,                                             -- EI_OSABI    = System V
  0x00,                                             -- EI_ABIVERSION
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,         -- EI_PAD × 7
  -- rest of Elf64_Ehdr (48 bytes) ───────────────────────────────────────
  0x03, 0x00,                                       -- e_type      = ET_DYN (3)
  0x3e, 0x00,                                       -- e_machine   = EM_X86_64 (62)
  0x01, 0x00, 0x00, 0x00,                           -- e_version
  0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- e_entry     = 0x100
  0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- e_phoff     = 64
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- e_shoff     = 0 (stripped)
  0x00, 0x00, 0x00, 0x00,                           -- e_flags
  0x40, 0x00,                                       -- e_ehsize    = 64
  0x38, 0x00,                                       -- e_phentsize = 56
  0x02, 0x00,                                       -- e_phnum     = 2
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00                -- e_shentsize/num/strndx
]⟩

#guard RawEhdr.fixtureBytes.size == 64

section Example

open RawEhdr

private def parsedEhdr : Option RawEhdr :=
  (Parser.run fixtureBytes (BytesDecode.decode : Parser RawEhdr)).toOption

#guard parsedEhdr.map (·.ei_class)       = some .class64   -- ELFCLASS64
#guard parsedEhdr.map (·.ei_data)        = some .lsb       -- ELFDATA2LSB
#guard parsedEhdr.map (·.ei_version)     = some .current   -- EV_CURRENT
#guard parsedEhdr.map (·.ei_osabi)       = some .none      -- ELFOSABI_NONE
#guard parsedEhdr.map (·.e_type)         = some .dyn       -- ET_DYN — ByteMap-validated
#guard parsedEhdr.map (·.e_machine)      = some .x86_64    -- EM_X86_64 — ByteMap-validated
#guard parsedEhdr.map (·.e_version)      = some .current   -- EV_CURRENT
#guard parsedEhdr.map (·.e_entry)        = some 0x100
#guard parsedEhdr.map (·.e_phoff)        = some 64
#guard parsedEhdr.map (·.e_phnum)        = some 2
#guard parsedEhdr.map (·.e_phentsize)    = some 56
#guard parsedEhdr.map (·.e_shoff)        = some 0
#guard parsedEhdr.map (·.e_shstrndx)     = some .undef     -- SHN_UNDEF

-- ── ByteMap rejection: unknown header tags fail decode ─────────────
-- Fixture with `e_type = 0xff00` (not in gabi-named set) and otherwise
-- valid bytes — parsing fails inside the `e_type` decode.
private def badEhdrBytes : ByteArray :=
  let bytes := fixtureBytes.toList.toArray
  let bytes := bytes.set! 0x10 0x00  -- e_type low byte
  let bytes := bytes.set! 0x11 0xff  -- e_type high byte = 0xff00
  ⟨bytes⟩
#guard (Parser.run badEhdrBytes (BytesDecode.decode : Parser RawEhdr)).toOption.isNone

-- Unknown EI_CLASS rejects before the post-ident fields are decoded.
private def badClassBytes : ByteArray :=
  let bytes := fixtureBytes.toList.toArray
  let bytes := bytes.set! 0x04 0xff
  ⟨bytes⟩
#guard (Parser.run badClassBytes (BytesDecode.decode : Parser RawEhdr)).toOption.isNone

-- Invalid EV_NONE in either version field fails decode; RawEhdr only
-- carries the currently valid `EV_CURRENT` case (gabi 02).
private def badIdentVersionBytes : ByteArray :=
  let bytes := fixtureBytes.toList.toArray
  let bytes := bytes.set! 0x06 0x00
  ⟨bytes⟩
#guard (Parser.run badIdentVersionBytes (BytesDecode.decode : Parser RawEhdr)).toOption.isNone

private def badFileVersionBytes : ByteArray :=
  let bytes := fixtureBytes.toList.toArray
  let bytes := bytes.set! 0x14 0x00
  let bytes := bytes.set! 0x15 0x00
  let bytes := bytes.set! 0x16 0x00
  let bytes := bytes.set! 0x17 0x00
  ⟨bytes⟩
#guard (Parser.run badFileVersionBytes (BytesDecode.decode : Parser RawEhdr)).toOption.isNone

-- `EI_OSABI` is typed but permissive: the gABI reserves 64..255 for
-- arch/psABI-specific meanings, so parsing preserves those values.
private def archOsabiBytes : ByteArray :=
  let bytes := fixtureBytes.toList.toArray
  let bytes := bytes.set! 0x07 0x40
  ⟨bytes⟩
#guard (Parser.run archOsabiBytes (BytesDecode.decode : Parser RawEhdr)).toOption.map
  (·.ei_osabi) = some (.archSpecific 0x40)

-- `e_shstrndx` decodes the gABI extended-index sentinel.
private def xindexBytes : ByteArray :=
  let bytes := fixtureBytes.toList.toArray
  let bytes := bytes.set! 0x3e 0xff
  let bytes := bytes.set! 0x3f 0xff
  ⟨bytes⟩
#guard (Parser.run xindexBytes (BytesDecode.decode : Parser RawEhdr)).toOption.map
  (·.e_shstrndx) = some .xindex

-- ── Error cases ──────────────────────────────────────────────────────
-- Wrong magic: first byte `0x00` instead of `0x7f`. The `Magic` field's
-- own BytesDecode instance checks all four magic bytes up-front and
-- short-circuits the whole RawEhdr decode before any other byte is read.
#guard (Parser.run ⟨#[0x00, 0x45, 0x4c, 0x46]⟩
          (BytesDecode.decode : Parser RawEhdr)).toOption.isNone

-- Truncated ident: only 4 bytes of magic — `ei_class` read hits EOF.
private def truncatedMagic : ByteArray := ⟨#[0x7f, 0x45, 0x4c, 0x46]⟩
#guard (Parser.run truncatedMagic (BytesDecode.decode : Parser RawEhdr)).toOption.isNone

-- Partial decode: 32 bytes (full ident + 16 bytes of post-ident) when
-- 64 needed. Magic + ident succeed; `e_entry`'s u64 read hits EOF.
private def halfEhdr : ByteArray := fixtureBytes.extract 0 32
#guard (Parser.run halfEhdr (BytesDecode.decode : Parser RawEhdr)).toOption.isNone

end Example

end LeanLoad.Parse

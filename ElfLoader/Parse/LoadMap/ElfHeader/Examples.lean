/-
Examples and fixture bytes for `Parse/LoadMap/ElfHeader/Basic.lean`.
-/

import ElfLoader.Parse.LoadMap.ElfHeader.Basic

namespace ElfLoader.Parse.Examples

/-- 64-byte ELF header fixture: 64-bit, little-endian, x86-64, ET_DYN,
    with two program headers at file offset 0x40 (matching
    `programHeaderBytes`). `e_entry = 0x100` points inside the
    lone PT_LOAD of `Parse.Examples.fixtureMainBytes` so the checked-parse
    entry-in-segment check passes. Section headers stripped
    (`e_shoff = 0`, `e_shnum = 0`); a loader doesn't need them. -/
def elfHeaderBytes : ByteArray := ⟨#[
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

#guard elfHeaderBytes.size == ElfHeaderSize

def rawEhdr? : Option RawElfHeader :=
  (Decodable.decode (α := RawElfHeader) elfHeaderBytes).toOption

#guard rawEhdr?.isSome

def elfHeaderFileSize : ByteSize := 0x208

def ehdr? : Option (ElfHeader elfHeaderFileSize) :=
  (ElfHeader.decoder elfHeaderFileSize).decode? elfHeaderBytes

#guard ehdr?.isSome

def ehdr : ElfHeader elfHeaderFileSize :=
  ehdr?.get (by native_decide)

#guard ehdr.ident.ei_class       = .class64   -- ELFCLASS64
#guard ehdr.ident.ei_data        = .lsb       -- ELFDATA2LSB
#guard ehdr.ident.ei_version     = .current   -- EV_CURRENT
#guard ehdr.ident.ei_osabi       = .none      -- ELFOSABI_NONE
#guard ehdr.e_type         = .dyn       -- ET_DYN — DecodableFromScalar-validated
#guard ehdr.e_machine      = .x86_64    -- EM_X86_64 — DecodableFromScalar-validated
#guard ehdr.e_version      = .current   -- EV_CURRENT
#guard ehdr.e_entry        = 0x100
#guard ehdr.e_phoff        = 64
#guard ehdr.e_phnum        = 2
#guard ehdr.e_phentsize    = 56
#guard ehdr.e_shoff        = 0
#guard ehdr.e_shstrndx     = .undef     -- SHN_UNDEF
#guard ehdr.programHeaderRange.off = 64
#guard ehdr.programHeaderRange.size =
  ByteSize.ofEntries 2 (Decodable.byteSize (α := RawProgramHeader))

def ehdrTooSmallFile? : Option (ElfHeader 0x80) :=
  (ElfHeader.decoder 0x80).decode? elfHeaderBytes

#guard ehdrTooSmallFile?.isNone

-- ── DecodableFromScalar rejection: unknown header tags fail decode ───────────
-- Fixture with `e_type = 0xff00` (not in gabi-named set) and otherwise
-- valid bytes — parsing fails inside the `e_type` decode.
def badElfHeaderTypeBytes : ByteArray :=
  let bytes := elfHeaderBytes.toList.toArray
  let bytes := bytes.set! 0x10 0x00  -- e_type low byte
  let bytes := bytes.set! 0x11 0xff  -- e_type high byte = 0xff00
  ⟨bytes⟩
#guard (Decodable.decode (α := RawElfHeader) badElfHeaderTypeBytes).toOption.isNone

-- Unknown EI_CLASS rejects before the post-ident fields are decoded.
def badElfHeaderClassBytes : ByteArray :=
  let bytes := elfHeaderBytes.toList.toArray
  let bytes := bytes.set! 0x04 0xff
  ⟨bytes⟩
#guard (Decodable.decode (α := RawElfHeader) badElfHeaderClassBytes).toOption.isNone

-- Invalid EV_NONE in either version field fails decode; RawElfHeader only
-- carries the currently valid `EV_CURRENT` case (gabi 02).
def badElfHeaderIdentVersionBytes : ByteArray :=
  let bytes := elfHeaderBytes.toList.toArray
  let bytes := bytes.set! 0x06 0x00
  ⟨bytes⟩
#guard (Decodable.decode (α := RawElfHeader) badElfHeaderIdentVersionBytes).toOption.isNone

def badElfHeaderFileVersionBytes : ByteArray :=
  let bytes := elfHeaderBytes.toList.toArray
  let bytes := bytes.set! 0x14 0x00
  let bytes := bytes.set! 0x15 0x00
  let bytes := bytes.set! 0x16 0x00
  let bytes := bytes.set! 0x17 0x00
  ⟨bytes⟩
#guard (Decodable.decode (α := RawElfHeader) badElfHeaderFileVersionBytes).toOption.isNone

-- ElfLoader policy rejects non-64-bit, big-endian, ET_EXEC, and unexpected
-- fixed record sizes while decoding the checked `ElfHeader`.
def class32ElfHeaderBytes : ByteArray :=
  let bytes := elfHeaderBytes.toList.toArray
  let bytes := bytes.set! 0x04 0x01
  ⟨bytes⟩
#guard (ElfHeader.decoder elfHeaderFileSize).decode? class32ElfHeaderBytes |>.isNone

def bigEndianElfHeaderBytes : ByteArray :=
  let bytes := elfHeaderBytes.toList.toArray
  let bytes := bytes.set! 0x05 0x02
  ⟨bytes⟩
#guard (ElfHeader.decoder elfHeaderFileSize).decode? bigEndianElfHeaderBytes |>.isNone

def execElfHeaderBytes : ByteArray :=
  let bytes := elfHeaderBytes.toList.toArray
  let bytes := bytes.set! 0x10 0x02
  ⟨bytes⟩
#guard (ElfHeader.decoder elfHeaderFileSize).decode? execElfHeaderBytes |>.isNone

def wrongElfHeaderSizeBytes : ByteArray :=
  let bytes := elfHeaderBytes.toList.toArray
  let bytes := bytes.set! 0x34 0x20
  let bytes := bytes.set! 0x35 0x00
  ⟨bytes⟩
#guard (ElfHeader.decoder elfHeaderFileSize).decode? wrongElfHeaderSizeBytes |>.isNone

def wrongProgramHeaderSizeBytes : ByteArray :=
  let bytes := elfHeaderBytes.toList.toArray
  let bytes := bytes.set! 0x36 0x40
  let bytes := bytes.set! 0x37 0x00
  ⟨bytes⟩
#guard (ElfHeader.decoder elfHeaderFileSize).decode? wrongProgramHeaderSizeBytes |>.isNone

-- `EI_OSABI` is typed but permissive: the gABI reserves 64..255 for
-- arch/psABI-specific meanings, so parsing preserves those values.
def elfHeaderArchOsabiBytes : ByteArray :=
  let bytes := elfHeaderBytes.toList.toArray
  let bytes := bytes.set! 0x07 0x40
  ⟨bytes⟩
#guard (Decodable.decode (α := RawElfHeader) elfHeaderArchOsabiBytes).toOption.map (·.ident.ei_osabi) =
  some (.archSpecific 0x40)

-- `e_shstrndx` decodes the gABI extended-index sentinel.
def elfHeaderXindexBytes : ByteArray :=
  let bytes := elfHeaderBytes.toList.toArray
  let bytes := bytes.set! 0x3e 0xff
  let bytes := bytes.set! 0x3f 0xff
  ⟨bytes⟩
#guard (Decodable.decode (α := RawElfHeader) elfHeaderXindexBytes).toOption.map (·.e_shstrndx) =
  some .xindex

-- ── Error cases ──────────────────────────────────────────────────────
-- Wrong magic: first byte `0x00` instead of `0x7f`. `IdentMagic` rejects the
-- decoded little-endian magic word.
def badMagicElfHeaderBytes : ByteArray :=
  let bytes := elfHeaderBytes.toList.toArray
  let bytes := bytes.set! 0x00 0x00
  ⟨bytes⟩
#guard (Decodable.decode (α := RawElfHeader) badMagicElfHeaderBytes).toOption.isNone

-- Truncated ident: only 4 bytes of magic — `ei_class` read hits EOF.
def truncatedElfHeaderMagicBytes : ByteArray := ⟨#[0x7f, 0x45, 0x4c, 0x46]⟩
#guard (Decodable.decode (α := RawElfHeader) truncatedElfHeaderMagicBytes).toOption.isNone

-- Partial decode: 32 bytes (full ident + 16 bytes of post-ident) when
-- 64 needed. Magic word + ident succeed; `e_entry`'s u64 read hits EOF.
def halfElfHeaderBytes : ByteArray := elfHeaderBytes.extract 0 32
#guard (Decodable.decode (α := RawElfHeader) halfElfHeaderBytes).toOption.isNone

end ElfLoader.Parse.Examples

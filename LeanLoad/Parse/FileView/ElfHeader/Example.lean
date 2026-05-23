/-
Examples and fixture bytes for `Parse/FileView/ElfHeader/Basic.lean`.
-/

import LeanLoad.Parse.FileView.ElfHeader.Basic

namespace LeanLoad.Parse.Example

/-- 64-byte ELF header fixture: 64-bit, little-endian, x86-64, ET_DYN,
    with two program headers at file offset 0x40 (matching
    `programHeaderBytes`). `e_entry = 0x100` points inside the
    lone PT_LOAD of `Parse.Example.fixtureBytes` so the checked-parse
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

def ehdr? : Option ElfHeader :=
  decodeWith? elfHeaderBytes ElfHeader.parse

#guard ehdr?.isSome

def ehdr : ElfHeader :=
  ehdr?.get (by native_decide)

#guard ehdr.ei_class       = .class64   -- ELFCLASS64
#guard ehdr.ei_data        = .lsb       -- ELFDATA2LSB
#guard ehdr.ei_version     = .current   -- EV_CURRENT
#guard ehdr.ei_osabi       = .none      -- ELFOSABI_NONE
#guard ehdr.e_type         = .dyn       -- ET_DYN — RawDecode-validated
#guard ehdr.e_machine      = .x86_64    -- EM_X86_64 — RawDecode-validated
#guard ehdr.e_version      = .current   -- EV_CURRENT
#guard ehdr.e_entry        = 0x100
#guard ehdr.e_phoff        = 64
#guard ehdr.e_phnum        = 2
#guard ehdr.e_phentsize    = 56
#guard ehdr.e_shoff        = 0
#guard ehdr.e_shstrndx     = .undef     -- SHN_UNDEF

-- ── RawDecode rejection: unknown header tags fail decode ───────────
-- Fixture with `e_type = 0xff00` (not in gabi-named set) and otherwise
-- valid bytes — parsing fails inside the `e_type` decode.
def badElfHeaderTypeBytes : ByteArray :=
  let bytes := elfHeaderBytes.toList.toArray
  let bytes := bytes.set! 0x10 0x00  -- e_type low byte
  let bytes := bytes.set! 0x11 0xff  -- e_type high byte = 0xff00
  ⟨bytes⟩
#guard (decodeWith? badElfHeaderTypeBytes ElfHeader.parse).isNone

-- Unknown EI_CLASS rejects before the post-ident fields are decoded.
def badElfHeaderClassBytes : ByteArray :=
  let bytes := elfHeaderBytes.toList.toArray
  let bytes := bytes.set! 0x04 0xff
  ⟨bytes⟩
#guard (decodeWith? badElfHeaderClassBytes ElfHeader.parse).isNone

-- Invalid EV_NONE in either version field fails decode; ElfHeader only
-- carries the currently valid `EV_CURRENT` case (gabi 02).
def badElfHeaderIdentVersionBytes : ByteArray :=
  let bytes := elfHeaderBytes.toList.toArray
  let bytes := bytes.set! 0x06 0x00
  ⟨bytes⟩
#guard (decodeWith? badElfHeaderIdentVersionBytes ElfHeader.parse).isNone

def badElfHeaderFileVersionBytes : ByteArray :=
  let bytes := elfHeaderBytes.toList.toArray
  let bytes := bytes.set! 0x14 0x00
  let bytes := bytes.set! 0x15 0x00
  let bytes := bytes.set! 0x16 0x00
  let bytes := bytes.set! 0x17 0x00
  ⟨bytes⟩
#guard (decodeWith? badElfHeaderFileVersionBytes ElfHeader.parse).isNone

-- `EI_OSABI` is typed but permissive: the gABI reserves 64..255 for
-- arch/psABI-specific meanings, so parsing preserves those values.
def elfHeaderArchOsabiBytes : ByteArray :=
  let bytes := elfHeaderBytes.toList.toArray
  let bytes := bytes.set! 0x07 0x40
  ⟨bytes⟩
#guard (decodeWith? elfHeaderArchOsabiBytes ElfHeader.parse).map (·.ei_osabi) =
  some (.archSpecific 0x40)

-- `e_shstrndx` decodes the gABI extended-index sentinel.
def elfHeaderXindexBytes : ByteArray :=
  let bytes := elfHeaderBytes.toList.toArray
  let bytes := bytes.set! 0x3e 0xff
  let bytes := bytes.set! 0x3f 0xff
  ⟨bytes⟩
#guard (decodeWith? elfHeaderXindexBytes ElfHeader.parse).map (·.e_shstrndx) = some .xindex

-- ── Error cases ──────────────────────────────────────────────────────
-- Wrong magic: first byte `0x00` instead of `0x7f`. The `Magic` field's
-- own BytesDecode instance checks all four magic bytes up-front and
-- short-circuits the whole ElfHeader decode before any other byte is read.
#guard (decodeWith? ⟨#[0x00, 0x45, 0x4c, 0x46]⟩ ElfHeader.parse).isNone

-- Truncated ident: only 4 bytes of magic — `ei_class` read hits EOF.
def truncatedElfHeaderMagicBytes : ByteArray := ⟨#[0x7f, 0x45, 0x4c, 0x46]⟩
#guard (decodeWith? truncatedElfHeaderMagicBytes ElfHeader.parse).isNone

-- Partial decode: 32 bytes (full ident + 16 bytes of post-ident) when
-- 64 needed. Magic + ident succeed; `e_entry`'s u64 read hits EOF.
def halfElfHeaderBytes : ByteArray := elfHeaderBytes.extract 0 32
#guard (decodeWith? halfElfHeaderBytes ElfHeader.parse).isNone

end LeanLoad.Parse.Example

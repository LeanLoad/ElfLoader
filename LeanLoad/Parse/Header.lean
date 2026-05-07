/-
ELF identification and 64-bit ELF header — bytes only.

Spec: gabi 02 (`third_party/gabi/docsrc/elf/02-eheader.rst`) §§ ELF
Identification, ELF Header.

Type + byte-level parser. Magic-byte check (`expect "\x7fELF"`) is
genuinely structural — without it we don't know we're looking at an
ELF — so it lives here. The semantic checks (`ei_class == ELFCLASS64`,
`ei_data == ELFDATA2LSB`) live in `Elaborate.elaborate`.
-/

import LeanLoad.Parse.Bytes

namespace LeanLoad.Parse

-- ============================================================================
-- ELF magic bytes (the "\x7fELF" signature)
-- ============================================================================

def ELFMAG0 : UInt8 := 0x7f
def ELFMAG1 : UInt8 := 0x45
def ELFMAG2 : UInt8 := 0x4c
def ELFMAG3 : UInt8 := 0x46

-- ============================================================================
-- Raw e_ident — gabi 02 § ELF Identification.
--
-- The first 16 bytes of the file. Fields are kept as raw `UInt8`s;
-- semantic interpretation (ei_class → 32/64-bit, ei_data → LE/BE)
-- is `Elaborate`'s job.
-- ============================================================================

/-- The first 16 bytes of the file (`e_ident`), kept raw. -/
structure RawIdent where
  ei_class      : UInt8
  ei_data       : UInt8
  ei_version    : UInt8
  ei_osabi      : UInt8
  ei_abiversion : UInt8
  -- bytes 9..15 are EI_PAD; ignored
  deriving Repr, Inhabited

-- ============================================================================
-- Raw 64-bit ELF header — gabi 02 § ELF Header (Elf64_Ehdr).
-- ============================================================================

/-- 64-bit ELF file header, kept raw. Field layout matches `Elf64_Ehdr`
    in gabi 02; field types are `UInt8`/`UInt16`/`UInt32`/`UInt64`
    matching the on-disk widths. Semantic interpretation (e_type as
    an enum, e_machine as an enum, etc.) is `Elaborate`'s job. -/
structure RawEhdr where
  ident       : RawIdent
  e_type      : UInt16
  e_machine   : UInt16
  e_version   : UInt32
  e_entry     : UInt64
  e_phoff     : UInt64
  e_shoff     : UInt64
  e_flags     : UInt32
  e_ehsize    : UInt16
  e_phentsize : UInt16
  e_phnum     : UInt16
  e_shentsize : UInt16
  e_shnum     : UInt16
  e_shstrndx  : UInt16
  deriving Repr, Inhabited

end LeanLoad.Parse

-- ============================================================================
-- Byte-level parser.
-- ============================================================================

namespace LeanLoad.Parse.Header

open LeanLoad.Parse
open LeanLoad.Parse.Bytes

def parseIdent : Parser RawIdent := do
  expect #[ELFMAG0, ELFMAG1, ELFMAG2, ELFMAG3]
  let ei_class      ← u8
  let ei_data       ← u8
  let ei_version    ← u8
  let ei_osabi      ← u8
  let ei_abiversion ← u8
  skip 7  -- EI_PAD
  return { ei_class, ei_data, ei_version, ei_osabi, ei_abiversion }

/-- Parse a 64-bit ELF header. Performs the structural magic-byte
    check (rejects non-ELF input). Class/endian/etc. semantic checks
    are deferred to `Elaborate.elaborate`. -/
def parse : Parser RawEhdr := do
  let ident ← parseIdent
  let e_type      ← u16le
  let e_machine   ← u16le
  let e_version   ← u32le
  let e_entry     ← u64le
  let e_phoff     ← u64le
  let e_shoff     ← u64le
  let e_flags     ← u32le
  let e_ehsize    ← u16le
  let e_phentsize ← u16le
  let e_phnum     ← u16le
  let e_shentsize ← u16le
  let e_shnum     ← u16le
  let e_shstrndx  ← u16le
  return { ident, e_type, e_machine, e_version, e_entry, e_phoff, e_shoff,
           e_flags, e_ehsize, e_phentsize, e_phnum, e_shentsize, e_shnum,
           e_shstrndx }

end LeanLoad.Parse.Header

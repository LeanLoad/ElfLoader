/-
ELF identification and 64-bit ELF header.

Spec: gabi 02 (`third_party/gabi/docsrc/elf/02-eheader.rst`) §§ ELF
Identification, ELF Header.

LeanLoad commits to ELFCLASS64 + ELFDATA2LSB. `parse` rejects 32-bit and
big-endian inputs. `e_machine` is recorded but not checked here;
architecture validation happens in `Plan`.
-/

import LeanLoad.Parse.Bytes

namespace LeanLoad.Parse.Header

open LeanLoad.Parse
open LeanLoad.Parse.Bytes

-- ============================================================================
-- Constants — gabi 02 § ELF Identification, §§ Object File Types, e_machine
-- ============================================================================

-- Magic bytes ("\x7fELF")
def ELFMAG0 : UInt8 := 0x7f
def ELFMAG1 : UInt8 := 0x45
def ELFMAG2 : UInt8 := 0x4c
def ELFMAG3 : UInt8 := 0x46

-- e_ident[EI_CLASS]
def ELFCLASSNONE : UInt8 := 0
def ELFCLASS32   : UInt8 := 1
def ELFCLASS64   : UInt8 := 2

-- e_ident[EI_DATA]
def ELFDATANONE : UInt8 := 0
def ELFDATA2LSB : UInt8 := 1
def ELFDATA2MSB : UInt8 := 2

-- e_type (gabi 02 Table: Object File Types)
def ET_NONE : UInt16 := 0
def ET_REL  : UInt16 := 1
def ET_EXEC : UInt16 := 2
def ET_DYN  : UInt16 := 3
def ET_CORE : UInt16 := 4

-- e_machine (subset; full registry in gabi appendix `a-emachine.rst`)
def EM_X86_64  : UInt16 := 62
def EM_AARCH64 : UInt16 := 183

#guard ELFMAG0 = 0x7f
#guard ELFCLASS64 = 2
#guard ET_DYN = 3
#guard EM_X86_64 = 62

-- ============================================================================
-- ELF identification — gabi 02 § ELF Identification
-- ============================================================================

/-- The first 16 bytes of the file (`e_ident`). -/
structure Ident where
  ei_class      : UInt8
  ei_data       : UInt8
  ei_version    : UInt8
  ei_osabi      : UInt8
  ei_abiversion : UInt8
  -- bytes 9..15 are EI_PAD; ignored
  deriving Repr, Inhabited

def parseIdent : Parser Ident := do
  expect #[ELFMAG0, ELFMAG1, ELFMAG2, ELFMAG3]
  let ei_class      ← u8
  let ei_data       ← u8
  let ei_version    ← u8
  let ei_osabi      ← u8
  let ei_abiversion ← u8
  skip 7  -- EI_PAD
  return { ei_class, ei_data, ei_version, ei_osabi, ei_abiversion }

-- ============================================================================
-- ELF header — gabi 02 § ELF Header (Elf64_Ehdr)
-- ============================================================================

/-- 64-bit ELF file header. Field layout matches `Elf64_Ehdr` in gabi 02. -/
structure ElfHeader64 where
  ident       : Ident
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

/-- Parse a 64-bit little-endian ELF header. Rejects non-ELF, 32-bit, and
    big-endian inputs. `e_machine` is captured as-is. -/
def parse : Parser ElfHeader64 := do
  let ident ← parseIdent
  if ident.ei_class != ELFCLASS64 then
    throw s!"only ELFCLASS64 supported (got ei_class={ident.ei_class})"
  if ident.ei_data != ELFDATA2LSB then
    throw s!"only little-endian supported (got ei_data={ident.ei_data})"
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

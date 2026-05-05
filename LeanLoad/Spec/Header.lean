/-
ELF identification and 64-bit ELF header — gabi 02 spec.

Spec: gabi 02 (`third_party/gabi/docsrc/elf/02-eheader.rst`) §§ ELF
Identification, ELF Header.

Types and constants only — the byte-level parser lives in
`LeanLoad.Parse.Header`.
-/

namespace LeanLoad.Spec.Header

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

end LeanLoad.Spec.Header

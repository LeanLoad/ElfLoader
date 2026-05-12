/-
ELF byte structures — bytes only, no semantics.

Every type here is a one-to-one transcription of an `Elf64_*` C
struct from gabi (or a related ABI); each section header below cites
its source chapter. Semantic interpretation of these fields (enum
lifting, validation, gabi-mandated invariants, name resolution) lives
in `LeanLoad/Elaborate/`.

Per-struct `BytesDecode` instances are auto-derived from the field
types (`UInt8/16/32/64`, `Pad n`, `Magic bs`); the deriving handler
walks the constructor in field order. See `LeanLoad/Parse/Bytes.lean`
for the typeclass and `LeanLoad/Parse/Deriving.lean` for the handler.

Variable-length parsers (`.dynamic` array, GNU hash chain walking)
that don't fit the deriving pattern live in their own files
(`Parse/Dynamic.lean`, `Parse/GnuHash.lean`).
-/

import LeanLoad.Parse.Decode
import LeanLoad.Parse.Deriving

namespace LeanLoad.Parse

-- ============================================================================
-- gabi 02 § ELF Identification + § ELF Header (Elf64_Ehdr)
-- ============================================================================

/-- The first 16 bytes of the file (`e_ident`). The `magic` field
    encodes the structural `\x7fELF` check; `_pad` is gabi's
    7-byte `EI_PAD`. Semantic interpretation of the remaining
    bytes (`ei_class` → 32/64-bit, `ei_data` → LE/BE) is
    `Elaborate`'s job. -/
structure RawIdent where
  magic         : Magic [0x7f, 0x45, 0x4c, 0x46]
  ei_class      : UInt8
  ei_data       : UInt8
  ei_version    : UInt8
  ei_osabi      : UInt8
  ei_abiversion : UInt8
  _pad          : Pad 7
  deriving Repr, Inhabited, BytesDecode

section Example
-- Layout of the 16-byte `e_ident` from a typical x86-64 ELF:
--
--   0x7f 0x45 0x4c 0x46    magic (verified, not stored)
--   0x02                   ei_class      = ELFCLASS64
--   0x01                   ei_data       = ELFDATA2LSB
--   0x01                   ei_version
--   0x00                   ei_osabi      (System V)
--   0x00                   ei_abiversion
--   0x00 × 7               EI_PAD        (skipped, not stored)
private def identBytes : ByteArray := ⟨#[
  0x7f, 0x45, 0x4c, 0x46,
  0x02, 0x01, 0x01, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 ]⟩

-- First check the parse succeeds, then field values via `.get!`.
#guard (Parser.run identBytes (BytesDecode.decode : Parser RawIdent)).toOption.isSome

private def parsedIdent : RawIdent :=
  (Parser.run identBytes (BytesDecode.decode : Parser RawIdent)).toOption.get!

#guard parsedIdent.ei_class      == 0x02
#guard parsedIdent.ei_data       == 0x01
#guard parsedIdent.ei_version    == 0x01
#guard parsedIdent.ei_osabi      == 0x00
#guard parsedIdent.ei_abiversion == 0x00

-- Wrong magic → parse fails before reading any other field.
#guard (Parser.run ⟨#[0x00, 0x45, 0x4c, 0x46]⟩
          (BytesDecode.decode : Parser RawIdent)).toOption.isNone
end Example

/-- 64-bit ELF file header. Field layout matches `Elf64_Ehdr`. -/
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
  deriving Repr, Inhabited, BytesDecode

-- ============================================================================
-- gabi 04 § String Table.
--
-- `RawStrtab` is just a byte buffer; entries are NUL-terminated
-- C strings indexed by byte offset. Lookup (bytes → `String` via
-- UTF-8 decode) is interpretive, lives in `Elaborate`.
-- ============================================================================

abbrev RawStrtab := ByteArray

-- ============================================================================
-- gabi 05 § Symbol Table (Elf64_Sym)
-- ============================================================================

/-- 64-bit symbol entry. `st_info` packs binding (high nibble) and
    type (low nibble); accessors live in `Elaborate`. -/
structure RawSym where
  st_name  : UInt32   -- string table offset
  st_info  : UInt8    -- bind << 4 | type
  st_other : UInt8    -- visibility
  st_shndx : UInt16   -- section index (or `SHN_*` reserved value)
  st_value : UInt64
  st_size  : UInt64
  deriving Repr, Inhabited, BytesDecode

/-- Size of one `Elf64_Sym` on disk: 4+1+1+2+8+8 = 24. -/
def RawSymSize : Nat := 24

-- ============================================================================
-- gabi 06 § Relocation (Elf64_Rela)
-- ============================================================================

/-- 64-bit relocation entry with explicit addend. `r_addend` is stored
    as `UInt64`; per gabi 06 it is the bit pattern of an `Elf64_Sxword`
    (signed). Signed interpretation happens at apply time. We model
    only `Rela` (with addend); the `Rel` form is allowed by gabi but
    neither AArch64 nor x86-64 emits it for dynamic relocations.

    Bit-field accessors `sym` / `type` (which unpack `r_info`) live
    in `Elaborate` — they're interpretive, not byte-level decode. -/
structure RawRela where
  r_offset : UInt64
  r_info   : UInt64
  r_addend : UInt64
  deriving Repr, Inhabited, BytesDecode

/-- Size of one `Elf64_Rela` on disk: 8+8+8 = 24. -/
def RawRelaSize : Nat := 24

-- ============================================================================
-- gabi 07 § Program Header (Elf64_Phdr)
--
-- Only the two `p_type` values that `Parse.RawElf.parse` uses
-- navigationally (find the dynamic section, find the PT_LOAD
-- covering an offset) are defined here. The full enumeration of
-- `p_type` and `p_flags` lives in `Elaborate`.
-- ============================================================================

def PT_LOAD    : UInt32 := 1
def PT_DYNAMIC : UInt32 := 2

/-- 64-bit program header entry. Field layout matches `Elf64_Phdr`. -/
structure RawPhdr where
  p_type   : UInt32
  p_flags  : UInt32
  p_offset : UInt64
  p_vaddr  : UInt64
  p_paddr  : UInt64
  p_filesz : UInt64
  p_memsz  : UInt64
  p_align  : UInt64
  deriving Repr, Inhabited, BytesDecode

/-- Size of one `Elf64_Phdr` on disk: 4+4+8*6 = 56. -/
def RawPhdrSize : Nat := 56

-- ============================================================================
-- gabi 08 § Dynamic Section (Elf64_Dyn)
--
-- `d_tag` constants kept here are only those `Parse.RawElf.parse`
-- uses navigationally (find each section in the .dynamic array).
-- Interpretive constants (DT_FLAGS, DF_*, etc.) live in `Elaborate`.
-- ============================================================================

def DT_NULL          : UInt64 := 0
def DT_NEEDED        : UInt64 := 1
def DT_PLTRELSZ      : UInt64 := 2
def DT_HASH          : UInt64 := 4
def DT_STRTAB        : UInt64 := 5
def DT_SYMTAB        : UInt64 := 6
def DT_RELA          : UInt64 := 7
def DT_RELASZ        : UInt64 := 8
def DT_STRSZ         : UInt64 := 10
def DT_SONAME        : UInt64 := 14
def DT_RPATH         : UInt64 := 15
def DT_JMPREL        : UInt64 := 23
def DT_INIT_ARRAY    : UInt64 := 25
def DT_FINI_ARRAY    : UInt64 := 26
def DT_INIT_ARRAYSZ  : UInt64 := 27
def DT_FINI_ARRAYSZ  : UInt64 := 28
def DT_RUNPATH       : UInt64 := 29

/-- One entry of the `.dynamic` array. `d_un` holds either `d_val`
    (an integer) or `d_ptr` (a virtual address); the interpretation
    is controlled by `d_tag`. -/
structure RawDyn where
  d_tag : UInt64
  d_un  : UInt64
  deriving Repr, Inhabited, BytesDecode

/-- Size of one `Elf64_Dyn` on disk: 8+8 = 16. -/
def RawDynSize : Nat := 16

end LeanLoad.Parse

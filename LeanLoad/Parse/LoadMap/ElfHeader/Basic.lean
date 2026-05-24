/-
Checked ELF header after file-size-dependent range validation.
-/

import LeanLoad.Parse.LoadMap.ElfHeader.Raw
import LeanLoad.Parse.LoadMap.ProgramHeader.Basic
import LeanLoad.Parse.Basic
import LeanLoad.Runtime

namespace LeanLoad.Parse

/-- ELF header accepted by LeanLoad's load-map stage. Field layout matches
    `Elf64_Ehdr`, with LeanLoad's header policy attached as proof fields.

    The `e_ident` prefix and header tags are decoded through semantic field
    types; unknown or unsupported values fail decoding. The program-header table
    range is checked against the observed file size before any phdr read. -/
structure ElfHeader (fileSize : ByteSize) extends RawElfHeader where
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
  /-- The `Elf64_Phdr` table described by `e_phoff/e_phnum` is inside the file. -/
  phdrInBounds :
    e_phoff.toNat +
      (ByteSize.ofEntries e_phnum.toNat (Decodable.byteSize (α := RawProgramHeader))).toNat ≤
        fileSize.toNat
  deriving Repr

namespace ElfHeader

/-- Attach file-size-dependent phdr-table bounds to a byte-decoded header. -/
def ofRaw (fileSize : ByteSize) (raw : RawElfHeader) : Except String (ElfHeader fileSize) := do
  let size := ByteSize.ofEntries raw.e_phnum.toNat (Decodable.byteSize (α := RawProgramHeader))
  let ⟨hClass⟩ ← require (raw.ident.ei_class = .class64)
    "parse: non-64-bit ELF is unsupported; expected ELFCLASS64"
  let ⟨hData⟩ ← require (raw.ident.ei_data = .lsb)
    "parse: big-endian ELF is unsupported; expected ELFDATA2LSB"
  let ⟨hEhdrSize⟩ ← require (raw.e_ehsize.toNat = ElfHeaderSize)
    s!"parse: expected Elf64_Ehdr size {ElfHeaderSize}, got {raw.e_ehsize.toNat}"
  let ⟨hPhdrSize⟩ ← require (raw.e_phentsize.toNat = ProgramHeaderSize)
    s!"parse: expected Elf64_Phdr size {ProgramHeaderSize}, got {raw.e_phentsize.toNat}"
  let ⟨hNotExec⟩ ← require (raw.e_type ≠ .exec)
    "parse: ET_EXEC is unsupported; expected ET_DYN"
  let ⟨hPhdr⟩ ← require (raw.e_phoff.toNat + size.toNat ≤ fileSize.toNat)
    s!"parse: program header table at file offset 0x{raw.e_phoff.toNat} requested \
      {size.toNat} bytes, past file size {fileSize.toNat}"
  .ok { raw with
    class64 := hClass,
    littleEndian := hData,
    ehsizeOk := hEhdrSize,
    phentsizeOk := hPhdrSize,
    notExec := hNotExec,
    phdrInBounds := hPhdr }

/-- Decode a checked ELF header from the current byte-decoder cursor. -/
def decoder (fileSize : ByteSize) : Decoder (ElfHeader fileSize) := do
  let raw : RawElfHeader ← Decodable.decoder
  match ofRaw fileSize raw with
  | .ok header => return header
  | .error e   => throw e

/-- Checked file range for the `Elf64_Phdr` table described by this header. -/
def programHeaderRange (header : ElfHeader fileSize) : Runtime.FileRange fileSize :=
  { off := header.e_phoff
    size := ByteSize.ofEntries header.e_phnum.toNat (Decodable.byteSize (α := RawProgramHeader))
    inBounds := header.phdrInBounds }

end ElfHeader

end LeanLoad.Parse

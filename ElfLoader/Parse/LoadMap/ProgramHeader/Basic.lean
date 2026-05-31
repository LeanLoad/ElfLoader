/-
Checked program headers.

`RawProgramHeader` owns the fixed-width `Elf64_Phdr` byte layout. This file
attaches the file-size-independent program-header arithmetic witnesses plus the
observed file-size witness for the header's file image
`[p_offset, p_offset + p_filesz)`.
-/

import ElfLoader.Parse.LoadMap.ProgramHeader.Raw
import ElfLoader.Parse.Basic
import ElfLoader.Runtime

namespace ElfLoader.Parse

/-- Program header checked against the observed file size. -/
structure ProgramHeader (fileSize : ByteSize) extends RawProgramHeader where
  /-- The file image described by `p_offset/p_filesz` is contained in the file
      (gabi 07 § Program Header). -/
  fileInBounds : p_offset.toNat + p_filesz.toNat ≤ fileSize.toNat
  /-- The memory image `[p_vaddr, p_vaddr + p_memsz)` does not wrap UInt64
      (gabi 07 § Program Header). -/
  eaddrNoWrap : p_vaddr.toNat + p_memsz.toNat < 2 ^ 64
  /-- gABI 07 § Program Header: `p_align` is `0` or a power of two. -/
  alignPow2 : p_align = 0 ∨ (p_align &&& (p_align - 1)) = 0
  /-- gABI 07 § Program Header: `p_vaddr ≡ p_offset (mod p_align)`. -/
  alignCong : p_align = 0 ∨ p_vaddr.val % p_align = p_offset.val % p_align
  deriving Repr

namespace ProgramHeader

instance : Inhabited (ProgramHeader fileSize) where
  default :=
    { p_type := default,
      p_flags := default,
      p_offset := 0,
      p_vaddr := default,
      p_paddr := default,
      p_filesz := 0,
      p_memsz := default,
      p_align := default,
      fileInBounds := by
        simp [FileOff.toNat, ByteSize.toNat]
        have hOff : (FileOff.val 0).toNat = 0 := by decide
        have hSize : (ByteSize.val 0).toNat = 0 := by decide
        rw [hOff, hSize]
        exact Nat.zero_le _,
      eaddrNoWrap := by
        decide,
      alignPow2 := Or.inl rfl,
      alignCong := Or.inl rfl }

/-- Attach checked program-header witnesses to a byte-decoded program header. -/
def ofRaw (fileSize : ByteSize) (raw : RawProgramHeader) :
    Except String (ProgramHeader fileSize) := do
  let ⟨fileInBounds⟩ ← require
    (raw.p_offset.toNat + raw.p_filesz.toNat ≤ fileSize.toNat)
    s!"parse: program header file image at file offset 0x{raw.p_offset.toNat} \
      requested {raw.p_filesz.toNat} bytes, past file size {fileSize.toNat}"
  let ⟨eaddrNoWrap⟩ ← require
    (raw.p_vaddr.toNat + raw.p_memsz.toNat < 2 ^ 64)
    s!"parse: program header p_vaddr+p_memsz wraps UInt64 \
      (0x{raw.p_vaddr.toNat}+0x{raw.p_memsz.toNat})"
  let ⟨alignPow2⟩ ← require
    (raw.p_align = 0 ∨ (raw.p_align &&& (raw.p_align - 1)) = 0)
    s!"parse: program header p_align=0x{raw.p_align.toNat} \
      is not a power of 2 (gabi-07 § Program Header)"
  let ⟨alignCong⟩ ← require
    (raw.p_align = 0 ∨ raw.p_vaddr.val % raw.p_align = raw.p_offset.val % raw.p_align)
    "parse: program header alignment congruence violated \
      (gabi-07: p_vaddr ≡ p_offset mod p_align)"
  return {
    raw with
    fileInBounds,
    eaddrNoWrap,
    alignPow2,
    alignCong
  }

/-- Decode one checked program header from the current byte-decoder cursor. -/
def decoder (fileSize : ByteSize) : Decoder (ProgramHeader fileSize) := do
  let raw : RawProgramHeader ← Decodable.decoder
  match ofRaw fileSize raw with
  | .ok phdr => return phdr
  | .error e => throw e

/-- Decode exactly `count` checked program headers from the current byte-decoder cursor. -/
def arrayDecoder (fileSize : ByteSize) (count : Nat) :
    Decoder (Array (ProgramHeader fileSize)) :=
  Decoder.array count (decoder fileSize)

/-- Checked file image described by `p_offset`/`p_filesz` (gabi 07 § Program Header). -/
def fileRange (ph : ProgramHeader fileSize) : Runtime.FileRange fileSize :=
  { off := ph.p_offset, size := ph.p_filesz, inBounds := ph.fileInBounds }

end ProgramHeader

end ElfLoader.Parse

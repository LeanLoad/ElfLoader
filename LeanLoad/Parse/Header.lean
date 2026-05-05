/-
Byte-level parser for the ELF identification and 64-bit ELF header.
Spec types live in `LeanLoad.Spec.Header`.
-/

import LeanLoad.Parse.Bytes
import LeanLoad.Spec.Header

namespace LeanLoad.Parse.Header

open LeanLoad.Parse.Bytes
open LeanLoad.Spec.Header

def parseIdent : Parser Ident := do
  expect #[ELFMAG0, ELFMAG1, ELFMAG2, ELFMAG3]
  let ei_class      ← u8
  let ei_data       ← u8
  let ei_version    ← u8
  let ei_osabi      ← u8
  let ei_abiversion ← u8
  skip 7  -- EI_PAD
  return { ei_class, ei_data, ei_version, ei_osabi, ei_abiversion }

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

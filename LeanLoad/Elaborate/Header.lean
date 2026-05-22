/-
ELF header constants used at elaboration to validate `e_ident`'s
class/endian fields against the supported set.

`ElfClass`, `ElfData`, `ElfType`, and `ElfMachine` live in
`Parse/Header/Enums.lean`; `RawEhdr` carries them directly as field
types, validated at byte-decode time via their `ByteMap` instances.
Elaborate consumes the already-typed fields and enforces LeanLoad's
64-bit / little-endian policy.

Spec: gabi 02 (`third_party/gabi/docsrc/elf/02-eheader.rst`) § ELF
Identification.
-/

import LeanLoad.Parse.Header.Ehdr

namespace LeanLoad.Elaborate

-- ELF identification (gabi 02 § ELF Identification)
def ELFCLASS32  : LeanLoad.Parse.ElfClass := .class32
def ELFCLASS64  : LeanLoad.Parse.ElfClass := .class64
def ELFDATA2LSB : LeanLoad.Parse.ElfData := .lsb
def ELFDATA2MSB : LeanLoad.Parse.ElfData := .msb

end LeanLoad.Elaborate

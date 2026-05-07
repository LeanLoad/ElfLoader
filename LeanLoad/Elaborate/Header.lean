/-
ELF header constants — `ELFCLASS*`, `ELFDATA*`, `ET_*`.

Spec: gabi 02 (`third_party/gabi/docsrc/elf/02-eheader.rst`) § ELF
Identification and § Object File Types.

These live in `Elaborate` (not `Parse`) because they are *meanings*
attached to bytes the parser already read into `RawIdent` and
`RawEhdr`. `elaborate` uses `ELFCLASS64` / `ELFDATA2LSB` to gate ELF
class / endianness; planner code uses `ET_EXEC` / `ET_DYN` to decide
whether an object's mmap base is fixed or assigned.
-/

namespace LeanLoad.Elaborate

-- ELF identification (gabi 02 § ELF Identification)
def ELFCLASS64  : UInt8 := 2
def ELFDATA2LSB : UInt8 := 1

-- e_type (gabi 02 Table: Object File Types)
def ET_NONE : UInt16 := 0
def ET_REL  : UInt16 := 1
def ET_EXEC : UInt16 := 2
def ET_DYN  : UInt16 := 3
def ET_CORE : UInt16 := 4

end LeanLoad.Elaborate

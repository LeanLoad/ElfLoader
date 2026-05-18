/-
ELF header — `ELFCLASS*` / `ELFDATA*` constants used to validate
e_ident at elaboration, plus the `ElfType` and `Machine` enum lifts
over `e_type` / `e_machine`.

Spec: gabi 02 (`third_party/gabi/docsrc/elf/02-eheader.rst`) § ELF
Identification, § Object File Types, § Machine.

`ELFCLASS64` / `ELFDATA2LSB` are kept as plain `UInt8` constants
because `elaborate` compares raw `e_ident` bytes against them and
rejects mismatches. `ElfType` and `Machine`, by contrast, are the
*post-elaboration* views: planner/exec code matches `elf.elfType`
or `elf.machine` against named cases, not raw codes.
-/

import LeanLoad.Parse.RawEhdr

namespace LeanLoad.Elaborate

-- ELF identification (gabi 02 § ELF Identification)
def ELFCLASS64  : UInt8 := 2
def ELFDATA2LSB : UInt8 := 1

/-- gabi 02 Table: Object File Types — typed view of `e_type`. -/
inductive ElfType where
  | none
  | rel
  | exec
  | dyn
  | core
  deriving Repr, BEq, Inhabited

/-- Lift `e_type` from raw bytes. `none` for OS- or processor-
    specific codes outside the five gabi-named values; `elaborate`
    rejects those at the parse boundary. -/
def ElfType.ofRaw : UInt16 → Option ElfType
  | 0 => some .none
  | 1 => some .rel
  | 2 => some .exec
  | 3 => some .dyn
  | 4 => some .core
  | _ => Option.none

#guard ElfType.ofRaw 0 == some .none
#guard ElfType.ofRaw 2 == some .exec
#guard ElfType.ofRaw 3 == some .dyn
#guard ElfType.ofRaw 0xff00 == none

/-- gabi 02 § ELF Identification — `e_machine` typed view. We support
    only the two psABIs LeanLoad targets; everything else is rejected
    at elaboration. -/
inductive Machine where
  | x86_64
  | aarch64
  deriving Repr, BEq, Inhabited

/-- Lift `e_machine`. `none` for unsupported machines. -/
def Machine.ofRaw : UInt16 → Option Machine
  | 62  => some .x86_64
  | 183 => some .aarch64
  | _   => Option.none

#guard Machine.ofRaw 62  == some .x86_64
#guard Machine.ofRaw 183 == some .aarch64
#guard Machine.ofRaw 40  == none

end LeanLoad.Elaborate

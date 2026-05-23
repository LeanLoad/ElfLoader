/-
Examples for checked `Parse/FileView/Basic.lean`.
-/

import LeanLoad.Parse.FileView.Basic

namespace LeanLoad.Parse.FileView.Example

open LeanLoad.Parse

-- Two non-contiguous PT_LOADs (handcrafted, not byte-decoded) exercise
-- the `eaddr ≠ offset` case that the consolidated fixture's single PT_LOAD
-- (with `eaddr = offset = 0`) cannot surface alone.
def programHeaderVaTestSegments : Array ProgramHeader := #[
  { (default : ProgramHeader) with
    p_type := .load,
    p_vaddr := 0x1000, p_memsz := 0x1000,
    p_offset := 0x1000, p_filesz := 0x1000 },
  { (default : ProgramHeader) with
    p_type := .load,
    p_vaddr := 0x3000, p_memsz := 0x500,
    p_offset := 0x2000, p_filesz := 0x500 } ]

private def fileViewHeader : ElfHeader := default

private def programHeaderFileView? : Except String FileView :=
  FileView.ofHeaders 0x4000 fileViewHeader programHeaderVaTestSegments

private def mappedOff? (va : Eaddr) : Option FileOff :=
  match programHeaderFileView? with
  | .ok map =>
      let range : EaddrRange := { start := va, size := 1 }
      match FileView.mapRange map 0x4000 range with
      | .ok mapped => some mapped.fileOff
      | .error _   => none
  | .error _ => none

#guard mappedOff? 0x1000 = some 0x1000  -- first PT_LOAD, identity
#guard mappedOff? 0x1abc = some 0x1abc  -- inside first segment
#guard mappedOff? 0x3010 = some 0x2010  -- second PT_LOAD, eaddr ≠ offset
#guard mappedOff? 0x0fff = none         -- before everything
#guard mappedOff? 0x2500 = none         -- gap between segments
#guard mappedOff? 0x3500 = none         -- past the second segment

end LeanLoad.Parse.FileView.Example

/-
Examples for checked `Parse/ImageView/Basic.lean`.
-/

import LeanLoad.Parse.ImageView.Basic

namespace LeanLoad.Parse.ImageView.Example

open LeanLoad.Parse

-- Two non-contiguous PT_LOADs (handcrafted, not byte-decoded) exercise
-- the `eaddr ≠ offset` case that the consolidated fixture's single PT_LOAD
-- (with `eaddr = offset = 0`) cannot surface alone.
def phdrVaTestSegments : Array ProgramHeader := #[
  { (default : ProgramHeader) with
    p_type := .load,
    p_vaddr := 0x1000, p_memsz := 0x1000,
    p_offset := 0x1000, p_filesz := 0x1000 },
  { (default : ProgramHeader) with
    p_type := .load,
    p_vaddr := 0x3000, p_memsz := 0x500,
    p_offset := 0x2000, p_filesz := 0x500 } ]

private def fileViewHeader : ElfHeader :=
  { (default : ElfHeader) with
    ei_class := .class64,
    ei_data := .lsb,
    e_type := .dyn,
    e_ehsize := 64,
    e_phentsize := 56 }

private def phdrFileView? : Except String ImageView :=
  ImageView.ofHeaders 0x4000 fileViewHeader phdrVaTestSegments

private def mappedOff? (va : Eaddr) : Option FileOff :=
  match phdrFileView? with
  | .ok map =>
      let range : EaddrRange := { start := va, size := 1 }
      match ImageView.mapRange map 0x4000 range with
      | .ok mapped => some mapped.fileOff
      | .error _   => none
  | .error _ => none

#guard mappedOff? 0x1000 = some 0x1000  -- first PT_LOAD, identity
#guard mappedOff? 0x1abc = some 0x1abc  -- inside first segment
#guard mappedOff? 0x3010 = some 0x2010  -- second PT_LOAD, eaddr ≠ offset
#guard mappedOff? 0x0fff = none         -- before everything
#guard mappedOff? 0x2500 = none         -- gap between segments
#guard mappedOff? 0x3500 = none         -- past the second segment

private def wrongElfHeaderSize? : Except String ImageView :=
  ImageView.ofHeaders 0x4000 { fileViewHeader with e_ehsize := 32 } phdrVaTestSegments

private def wrongPhentsize? : Except String ImageView :=
  ImageView.ofHeaders 0x4000 { fileViewHeader with e_phentsize := 64 } phdrVaTestSegments

#guard
  match wrongElfHeaderSize? with
  | .ok _    => false
  | .error _ => true

#guard
  match wrongPhentsize? with
  | .ok _    => false
  | .error _ => true

end LeanLoad.Parse.ImageView.Example

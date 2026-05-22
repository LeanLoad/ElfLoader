/-
Examples for checked `Parse/Elf/LoadMap.lean`.
-/

import LeanLoad.Parse.Elf.LoadMap

namespace LeanLoad.Parse.Elf.LoadMap.Example

open LeanLoad.Parse

-- Two non-contiguous PT_LOADs (handcrafted, not byte-decoded) exercise
-- the `vaddr ≠ offset` case that the consolidated fixture's single PT_LOAD
-- (with `vaddr = offset = 0`) cannot surface alone.
def phdrVaTestSegments : Array Phdr := #[
  { (default : Phdr) with
    p_type := .load,
    p_vaddr := 0x1000, p_memsz := 0x1000,
    p_offset := 0x1000, p_filesz := 0x1000 },
  { (default : Phdr) with
    p_type := .load,
    p_vaddr := 0x3000, p_memsz := 0x500,
    p_offset := 0x2000, p_filesz := 0x500 } ]

private def loadMapHeader : Ehdr :=
  { (default : Ehdr) with
    ei_class := .class64,
    ei_data := .lsb,
    e_type := .dyn,
    e_ehsize := 64,
    e_phentsize := 56 }

private def phdrLoadMap? : Except String LoadMap :=
  LoadMap.ofHeaders 0x4000 loadMapHeader phdrVaTestSegments

private def mappedOff? (va : Vaddr) : Option FileOff :=
  match phdrLoadMap? with
  | .ok map =>
      match LoadMap.mapVaddr map va 1 with
      | .ok mapped => some mapped.off
      | .error _   => none
  | .error _ => none

#guard mappedOff? 0x1000 = some 0x1000  -- first PT_LOAD, identity
#guard mappedOff? 0x1abc = some 0x1abc  -- inside first segment
#guard mappedOff? 0x3010 = some 0x2010  -- second PT_LOAD, vaddr ≠ offset
#guard mappedOff? 0x0fff = none         -- before everything
#guard mappedOff? 0x2500 = none         -- gap between segments
#guard mappedOff? 0x3500 = none         -- past the second segment

private def wrongEhdrSize? : Except String LoadMap :=
  LoadMap.ofHeaders 0x4000 { loadMapHeader with e_ehsize := 32 } phdrVaTestSegments

private def wrongPhentsize? : Except String LoadMap :=
  LoadMap.ofHeaders 0x4000 { loadMapHeader with e_phentsize := 64 } phdrVaTestSegments

#guard
  match wrongEhdrSize? with
  | .ok _    => false
  | .error _ => true

#guard
  match wrongPhentsize? with
  | .ok _    => false
  | .error _ => true

end LeanLoad.Parse.Elf.LoadMap.Example

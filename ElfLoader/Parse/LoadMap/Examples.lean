/-
Examples for checked `Parse/LoadMap/Basic.lean`.
-/

import ElfLoader.Parse.LoadMap.Basic

namespace ElfLoader.Parse.LoadMap.Examples

open ElfLoader.Parse

private def loadMapFileSize : ByteSize := 0x4000

-- Two non-contiguous PT_LOADs (handcrafted, not byte-decoded) exercise
-- the `eaddr ≠ offset` case that the consolidated fixture's single PT_LOAD
-- (with `eaddr = offset = 0`) cannot surface alone.
def programHeaderVaTestSegments : Array (ProgramHeader loadMapFileSize) := #[
  { (default : ProgramHeader loadMapFileSize) with
    p_type := .load,
    p_vaddr := 0x1000, p_memsz := 0x1000,
    p_offset := 0x1000, p_filesz := 0x1000,
    fileInBounds := by decide,
    eaddrNoWrap := by decide,
    alignPow2 := by decide,
    alignCong := by decide },
  { (default : ProgramHeader loadMapFileSize) with
    p_type := .load,
    p_vaddr := 0x3000, p_memsz := 0x500,
    p_offset := 0x2000, p_filesz := 0x500,
    fileInBounds := by decide,
    eaddrNoWrap := by decide,
    alignPow2 := by decide,
    alignCong := by decide } ]

private def loadMapHeader : ElfHeader loadMapFileSize :=
  { ident :=
      { magic := .elf,
        ei_class := .class64,
        ei_data := .lsb,
        ei_version := .current,
        ei_osabi := .none,
        ei_abiversion := default,
        pad0 := 0, pad1 := 0, pad2 := 0, pad3 := 0, pad4 := 0, pad5 := 0, pad6 := 0 },
    e_type := .dyn,
    e_machine := default,
    e_version := .current,
    e_entry := default,
    e_phoff := default,
    e_shoff := default,
    e_flags := default,
    e_ehsize := 64,
    e_phentsize := 56,
    e_phnum := default,
    e_shentsize := default,
    e_shnum := default,
    e_shstrndx := .undef,
    class64 := rfl,
    littleEndian := rfl,
    ehsizeOk := by decide,
    phentsizeOk := by decide,
    notExec := by decide,
    phdrInBounds := by decide }

private def programHeaderLoadMap? : Except String (LoadMap loadMapFileSize) :=
  LoadMap.ofHeaders loadMapFileSize loadMapHeader programHeaderVaTestSegments

private def mappedOff? (va : Eaddr) : Option FileOff :=
  match programHeaderLoadMap? with
  | .ok map =>
      let range : EaddrRange := { start := va, size := 1 }
      match LoadMap.mapRange map range with
      | .ok mapped => some mapped.fileOff
      | .error _   => none
  | .error _ => none

#guard mappedOff? 0x1000 = some 0x1000  -- first PT_LOAD, identity
#guard mappedOff? 0x1abc = some 0x1abc  -- inside first segment
#guard mappedOff? 0x3010 = some 0x2010  -- second PT_LOAD, eaddr ≠ offset
#guard mappedOff? 0x0fff = none         -- before everything
#guard mappedOff? 0x2500 = none         -- gap between segments
#guard mappedOff? 0x3500 = none         -- past the second segment

end ElfLoader.Parse.LoadMap.Examples

/-
Examples and fixture bytes for `Parse/Phdr/Raw.lean`.
-/

import LeanLoad.Parse.Elf.LoadMap

namespace LeanLoad.Parse.Example

/-- 112-byte program-header fixture: one PT_LOAD covering the full
    488-byte file at `vaddr = offset = 0` (the convention every real
    linker uses so `AT_PHDR` calculations work without offset→vaddr
    translation), plus one PT_DYNAMIC pointing at the dynamic section at
    offset 0x128. Coordinated with `Elf.Example.fixtureBytes`. -/
def phdrBytes : ByteArray := ⟨#[
  -- Phdr[0]: PT_LOAD covering [0..0x1e8] ────────────────────────────────
  0x01, 0x00, 0x00, 0x00,                           -- p_type   = PT_LOAD
  0x05, 0x00, 0x00, 0x00,                           -- p_flags  = R|X = 5
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_offset = 0
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_vaddr  = 0
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_paddr  = 0
  0xe8, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_filesz = 0x1e8
  0xe8, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_memsz  = 0x1e8
  0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_align  = 0x1000
  -- Phdr[1]: PT_DYNAMIC ─────────────────────────────────────────────────
  0x02, 0x00, 0x00, 0x00,                           -- p_type   = PT_DYNAMIC
  0x06, 0x00, 0x00, 0x00,                           -- p_flags  = R|W = 6
  0x28, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_offset = 0x128
  0x28, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_vaddr  = 0x128
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_paddr  = 0
  0xc0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_filesz = 0xc0
  0xc0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_memsz  = 0xc0
  0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00    -- p_align  = 8
]⟩

#guard phdrBytes.size == 2 * RawPhdrSize  -- = 112

def phdrs? : Option (Array RawPhdr) :=
  parseBytes? phdrBytes (RawPhdr.parseTable 2)

#guard phdrs?.isSome

def phdrs : Array RawPhdr :=
  phdrs?.get (by native_decide)

#guard phdrs.size = 2

def loadPhdr : RawPhdr := (phdrs[0]?).getD default
def dynamicPhdr : RawPhdr := (phdrs[1]?).getD default

-- PT_LOAD
#guard loadPhdr.p_type   = .load
#guard loadPhdr.p_flags  = PhdrFlags.ofRaw 5 -- R|X
#guard loadPhdr.p_vaddr  = 0
#guard loadPhdr.p_filesz = 0x1e8
#guard loadPhdr.p_align  = 0x1000
-- PT_DYNAMIC
#guard dynamicPhdr.p_type   = .dynamic
#guard dynamicPhdr.p_offset = 0x128
#guard dynamicPhdr.p_filesz = 0xc0

-- ── Checked `LoadMap.mapVaddr` over a 2-phdr array ─────────────────────
-- Two non-contiguous PT_LOADs (handcrafted, not byte-decoded) exercise
-- the `vaddr ≠ offset` case that the fixture's single PT_LOAD (with
-- `vaddr = offset = 0`) can't surface alone.
def phdrVaTestSegments : Array RawPhdr := #[
  { (default : RawPhdr) with
    p_type := .load,
    p_vaddr := 0x1000, p_memsz := 0x1000,
    p_offset := 0x1000, p_filesz := 0x1000 },
  { (default : RawPhdr) with
    p_type := .load,
    p_vaddr := 0x3000, p_memsz := 0x500,
    p_offset := 0x2000, p_filesz := 0x500 } ]

private def loadMapHeader : Ehdr :=
  { (default : Ehdr) with ei_class := .class64, ei_data := .lsb, e_type := .dyn }

private def phdrLoadMap? : Except String Elf.LoadMap :=
  Elf.LoadMap.ofHeaders 0x4000 loadMapHeader phdrVaTestSegments

private def mappedOff? (va : Vaddr) : Option FileOff :=
  match phdrLoadMap? with
  | .ok map =>
      match Elf.LoadMap.mapVaddr map va 1 with
      | .ok mapped => some mapped.off
      | .error _   => none
  | .error _ => none

#guard mappedOff? 0x1000 = some 0x1000  -- first PT_LOAD, identity
#guard mappedOff? 0x1abc = some 0x1abc  -- inside first segment
#guard mappedOff? 0x3010 = some 0x2010  -- second PT_LOAD, vaddr ≠ offset
#guard mappedOff? 0x0fff = none         -- before everything
#guard mappedOff? 0x2500 = none         -- gap between segments
#guard mappedOff? 0x3500 = none         -- past the second segment

-- ── Error cases ──────────────────────────────────────────────────────
-- Truncated phdr: 20 bytes when 56 (RawPhdrSize) expected. EOF hits
-- inside the `p_offset` u64 read.
#guard
  (parseBytes? (phdrBytes.extract 0 20) RawPhdr.parse).isNone

-- `decodeArray` asking for 3 entries from a 2-entry buffer: third
-- entry hits EOF.
#guard
  (parseBytes? phdrBytes (RawPhdr.parseTable 3)).isNone

end LeanLoad.Parse.Example

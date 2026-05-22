/-
Examples and fixture bytes for `Parse/Phdr/Raw.lean`.
-/

import LeanLoad.Parse.Phdr.Raw

namespace LeanLoad.Parse.Example

/-- 112-byte program-header fixture: one PT_LOAD covering the full
    520-byte file at `vaddr = offset = 0` (the convention every real
    linker uses so `AT_PHDR` calculations work without offset→vaddr
    translation), plus one PT_DYNAMIC pointing at the dynamic section at
    offset 0x128. Coordinated with `Elf.Example.fixtureBytes`. -/
def phdrBytes : ByteArray := ⟨#[
  -- Phdr[0]: PT_LOAD covering [0..0x208] ────────────────────────────────
  0x01, 0x00, 0x00, 0x00,                           -- p_type   = PT_LOAD
  0x05, 0x00, 0x00, 0x00,                           -- p_flags  = R|X = 5
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_offset = 0
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_vaddr  = 0
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_paddr  = 0
  0x08, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_filesz = 0x208
  0x08, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_memsz  = 0x208
  0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_align  = 0x1000
  -- Phdr[1]: PT_DYNAMIC ─────────────────────────────────────────────────
  0x02, 0x00, 0x00, 0x00,                           -- p_type   = PT_DYNAMIC
  0x06, 0x00, 0x00, 0x00,                           -- p_flags  = R|W = 6
  0x28, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_offset = 0x128
  0x28, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_vaddr  = 0x128
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_paddr  = 0
  0xe0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_filesz = 0xe0
  0xe0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_memsz  = 0xe0
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
#guard loadPhdr.p_filesz = 0x208
#guard loadPhdr.p_align  = 0x1000
-- PT_DYNAMIC
#guard dynamicPhdr.p_type   = .dynamic
#guard dynamicPhdr.p_offset = 0x128
#guard dynamicPhdr.p_filesz = 0xe0

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

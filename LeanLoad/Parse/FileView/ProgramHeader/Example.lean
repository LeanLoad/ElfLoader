/-
Examples and fixture bytes for `Parse/FileView/ProgramHeader/Basic.lean`.
-/

import LeanLoad.Parse.FileView.ProgramHeader.Basic

namespace LeanLoad.Parse.Example

/-- 112-byte program-header fixture: one PT_LOAD covering the full 520-byte file
    at `eaddr = offset = 0` (the normal linker shape, though checked parse can
    translate non-identity `p_offset`/`p_vaddr` pairs), plus one PT_DYNAMIC
    pointing at the dynamic section at offset 0x128. Coordinated with
    `Parse.Example.fixtureBytes`. -/
def programHeaderBytes : ByteArray := ⟨#[
  -- ProgramHeader[0]: PT_LOAD covering [0..0x208] ────────────────────────────────
  0x01, 0x00, 0x00, 0x00,                           -- p_type   = PT_LOAD
  0x05, 0x00, 0x00, 0x00,                           -- p_flags  = R|X = 5
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_offset = 0
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_vaddr  = 0
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_paddr  = 0
  0x08, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_filesz = 0x208
  0x08, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_memsz  = 0x208
  0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_align  = 0x1000
  -- ProgramHeader[1]: PT_DYNAMIC ─────────────────────────────────────────────────
  0x02, 0x00, 0x00, 0x00,                           -- p_type   = PT_DYNAMIC
  0x06, 0x00, 0x00, 0x00,                           -- p_flags  = R|W = 6
  0x28, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_offset = 0x128
  0x28, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_vaddr  = 0x128
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_paddr  = 0
  0xe0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_filesz = 0xe0
  0xe0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_memsz  = 0xe0
  0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00    -- p_align  = 8
]⟩

#guard programHeaderBytes.size == 2 * ProgramHeaderSize  -- = 112

def programHeaders? : Option (Array ProgramHeader) :=
  decodeWith? programHeaderBytes (ProgramHeader.parseTable 2)

#guard programHeaders?.isSome

def programHeaders : Array ProgramHeader :=
  programHeaders?.get (by native_decide)

#guard programHeaders.size = 2

def loadProgramHeader : ProgramHeader := (programHeaders[0]?).getD default
def dynamicProgramHeader : ProgramHeader := (programHeaders[1]?).getD default

-- PT_LOAD
#guard loadProgramHeader.p_type   = .load
#guard loadProgramHeader.p_flags  = ProgramHeaderFlags.ofRaw 5 -- R|X
#guard loadProgramHeader.p_vaddr  = 0
#guard loadProgramHeader.p_filesz = 0x208
#guard loadProgramHeader.p_align  = 0x1000
-- PT_DYNAMIC
#guard dynamicProgramHeader.p_type   = .dynamic
#guard dynamicProgramHeader.p_offset = 0x128
#guard dynamicProgramHeader.p_filesz = 0xe0

-- ── Error cases ──────────────────────────────────────────────────────
-- Truncated phdr: 20 bytes when 56 (ProgramHeaderSize) expected. EOF hits
-- inside the `p_offset` u64 read.
#guard
  (decodeWith? (programHeaderBytes.extract 0 20) ProgramHeader.parse).isNone

-- `decodeArray` asking for 3 entries from a 2-entry buffer: third
-- entry hits EOF.
#guard
  (decodeWith? programHeaderBytes (ProgramHeader.parseTable 3)).isNone

end LeanLoad.Parse.Example

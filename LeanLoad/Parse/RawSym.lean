/-
gabi 05 § Symbol Table — `Elf64_Sym` entry.

`st_info` packs binding (high nibble) and type (low nibble) in a
single byte; bit-field accessors live in `Elaborate/Symbol.lean`.
-/

import LeanLoad.Parse.Decode
import LeanLoad.Parse.Deriving

namespace LeanLoad.Parse

/-- 64-bit symbol entry. -/
structure RawSym where
  st_name  : UInt32   -- string table offset
  st_info  : UInt8    -- bind << 4 | type
  st_other : UInt8    -- visibility
  st_shndx : UInt16   -- section index (or `SHN_*` reserved value)
  st_value : UInt64
  st_size  : UInt64
  deriving Repr, Inhabited, BytesDecode

/-- Size of one `Elf64_Sym` on disk: 4+1+1+2+8+8 = 24. -/
def RawSymSize : Nat := 24

/-- 48-byte symbol-table fixture: the mandatory NULL symbol at index 0
    and a global undefined `printf` reference at index 1. Real
    `.dynsym` always reserves index 0 for the all-zero NULL entry
    (gabi 05). The entry count is normally derived from `DT_HASH.nchain`
    in the consolidated fixture (where `nchain = 2`). The second
    symbol's `st_name = 11` indexes into `Parse.RawStrtab.fixtureBytes`
    at the start of "printf". -/
def RawSym.fixtureBytes : ByteArray := ⟨#[
  -- Sym[0]: NULL ────────────────────────────────────────────────────────
  0x00, 0x00, 0x00, 0x00,                           -- st_name
  0x00,                                             -- st_info
  0x00,                                             -- st_other
  0x00, 0x00,                                       -- st_shndx
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- st_value
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- st_size
  -- Sym[1]: undef "printf" ──────────────────────────────────────────────
  0x0b, 0x00, 0x00, 0x00,                           -- st_name  = 11 (strtab offset)
  0x10,                                             -- st_info  = STB_GLOBAL << 4 | STT_NOTYPE
  0x00,                                             -- st_other
  0x00, 0x00,                                       -- st_shndx = SHN_UNDEF (0)
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- st_value = 0 (undef)
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00    -- st_size  = 0
]⟩

#guard RawSym.fixtureBytes.size == 2 * RawSymSize  -- = 48

section Example

open RawSym

private def parsedSymtab : Option (Array RawSym) :=
  (Parser.run fixtureBytes (decodeArray (α := RawSym) 0 2)).toOption

#guard parsedSymtab.map (·.size) = some 2
-- NULL symbol — every field is zero.
#guard (parsedSymtab.bind (·[0]?)).map (·.st_name)  = some 0
#guard (parsedSymtab.bind (·[0]?)).map (·.st_info)  = some 0
#guard (parsedSymtab.bind (·[0]?)).map (·.st_shndx) = some 0
-- printf reference — st_info encodes STB_GLOBAL (1<<4) | STT_NOTYPE (0).
#guard (parsedSymtab.bind (·[1]?)).map (·.st_name)  = some 11
#guard (parsedSymtab.bind (·[1]?)).map (·.st_info)  = some 0x10
#guard (parsedSymtab.bind (·[1]?)).map (·.st_shndx) = some 0  -- SHN_UNDEF

-- ── Error cases ──────────────────────────────────────────────────────
-- Truncated sym: 10 bytes when 24 (RawSymSize) expected — EOF inside
-- the `st_value` u64 read.
#guard
  (Parser.run (fixtureBytes.extract 0 10) (BytesDecode.decode : Parser RawSym)).toOption.isNone

-- `decodeArray` asking for 3 entries from a 2-entry (48-byte) buffer —
-- third entry hits EOF.
#guard
  (Parser.run fixtureBytes (decodeArray (α := RawSym) 0 3)).toOption.isNone

end Example

end LeanLoad.Parse

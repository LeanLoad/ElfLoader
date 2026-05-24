/-
gabi 05 § Symbol Table — `Elf64_Sym` entry.

`st_info` packs binding (high nibble) and type (low nibble) in a
single byte; bit-field accessors live in `Parse/Dynamic/Symbol/Checked.lean`.
-/

import LeanLoad.Parse.Decode.Decodable
import LeanLoad.Parse.Decode.Deriving
import LeanLoad.Parse.Address

namespace LeanLoad.Parse

/-- 64-bit symbol entry. -/
structure RawSym where
  st_name  : UInt32   -- string table offset
  st_info  : UInt8    -- bind << 4 | type
  st_other : UInt8    -- visibility
  st_shndx : UInt16   -- section index (or `SHN_*` reserved value)
  st_value : UInt64
  st_size  : UInt64
  deriving Repr, Inhabited, Decodable

/-- Size of one `Elf64_Sym` on disk: 4+1+1+2+8+8 = 24. -/
def RawSymSize : Nat := 24

/-- Dynamic symbol table — the on-disk array of `RawSym` entries
    pointed at by `DT_SYMTAB`. Count comes from `DT_HASH.nchain`. -/
abbrev RawSymtab := Array RawSym

namespace RawSymtab

/-- Byte extent for `count` `Elf64_Sym` entries. -/
def tableByteSize (count : Nat) : ByteSize :=
  ByteSize.ofEntries count RawSymSize

/-- Decode `count` consecutive dynamic-symbol entries. -/
def decode (count : Nat) : Decoder RawSymtab :=
  Decoder.array count (Decodable.decoder (α := RawSym))

end RawSymtab

/-- 48-byte symbol-table fixture: the mandatory NULL symbol at index 0
    and a global undefined `printf` reference at index 1. Real
    `.dynsym` always reserves index 0 for the all-zero NULL entry
    (gabi 05). The entry count is normally derived from `DT_HASH.nchain`
    in the consolidated fixture (where `nchain = 2`). The second
    symbol's `st_name = 11` indexes into `Strtab.fixtureBytes` at
    the start of "printf". -/
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
  Decoder.run? fixtureBytes (Decoder.array 2 (Decodable.decoder (α := RawSym)))

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
  (Decoder.run? (fixtureBytes.extract 0 10) (Decodable.decoder (α := RawSym))).isNone

-- `Decoder.array` asking for 3 entries from a 2-entry (48-byte) buffer —
-- third entry hits EOF.
#guard
  (Decoder.run? fixtureBytes (Decoder.array 3 (Decodable.decoder (α := RawSym)))).isNone

end Example

end LeanLoad.Parse

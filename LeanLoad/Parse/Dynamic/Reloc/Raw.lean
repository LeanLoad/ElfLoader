/-
gabi 06 § Relocation — `Elf64_Rela` entry (with explicit addend).

`r_addend` is stored as `UInt64`; per gabi 06 it is the bit pattern
of an `Elf64_Sxword` (signed). Signed interpretation happens at apply
time. We model only `Reloc` (with addend); the `Rel` form is allowed
by gabi but neither AArch64 nor x86-64 emits it for dynamic
relocations.

Bit-field accessors `sym` / `type` (which unpack `r_info`) live in
`Layout/Reloc/ABI.lean` — they're interpretive, not byte-level decode.
-/

import LeanLoad.Parse.Decode.Decodable
import LeanLoad.Parse.Decode.Deriving
import LeanLoad.Parse.Address

namespace LeanLoad.Parse

/-- 64-bit relocation entry with explicit addend. -/
structure RawRela where
  r_offset : Eaddr
  r_info   : UInt64
  r_addend : UInt64
  deriving Repr, Inhabited, Decodable

#guard Decodable.byteSize (α := RawRela) = 24  -- gabi 06 § Relocation: `Elf64_Rela`

namespace RawRela

/-- Byte extent for `count` `Elf64_Rela` entries. -/
def tableByteSize (count : Nat) : ByteSize :=
  ByteSize.ofEntries count (Decodable.byteSize (α := RawRela))

/-- Convert a `DT_RELASZ`/`DT_PLTRELSZ` byte size into an entry count,
    rejecting sizes that are not a whole number of `Elf64_Rela` entries. -/
def countFromByteSize (size : ByteSize) : Except String Nat :=
  let entrySize := Decodable.byteSize (α := RawRela)
  let bytes := size.toNat
  if bytes % entrySize == 0 then
    .ok (bytes / entrySize)
  else
    .error s!"rela table byte size {bytes} is not a multiple of {entrySize}"

end RawRela

/-- 24-byte rela-table fixture: one `R_X86_64_RELATIVE` relocation at
    offset `0x100`. The `r_offset` lies inside the consolidated
    fixture's PT_LOAD memsz, so `Reloc.covered` accepts during checked
    parse. `r_info = 8` packs `(sym << 32) | type` with `sym = 0` and
    `type = 8 = R_X86_64_RELATIVE`; non-zero `sym` cases (e.g.
    `R_X86_64_GLOB_DAT`) live in the per-arch reloc tables and tests
    in `Layout/Reloc/ABI.lean`. -/
def RawRela.fixtureBytes : ByteArray := ⟨#[
  0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- r_offset = 0x100
  0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- r_info   = 8 (sym=0, type=R_X86_64_RELATIVE)
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00    -- r_addend = 0
]⟩

#guard RawRela.fixtureBytes.size == Decodable.byteSize (α := RawRela)  -- = 24

section Example

open RawRela

private def parsedRelas : Option (Array RawRela) :=
  (Decodable.parseArray (α := RawRela) fixtureBytes 1).toOption

#guard parsedRelas.map (·.size) = some 1
#guard (parsedRelas.bind (·[0]?)).map (·.r_offset) = some 0x100
#guard (parsedRelas.bind (·[0]?)).map (·.r_info)   = some 8       -- R_X86_64_RELATIVE
#guard (parsedRelas.bind (·[0]?)).map (·.r_addend) = some 0

-- ── Error cases ──────────────────────────────────────────────────────
-- Truncated rela: 15 bytes when 24 expected — EOF inside the `r_info` u64 read.
#guard
  (Decodable.parse (α := RawRela) (fixtureBytes.extract 0 15)).toOption.isNone

-- `Decoder.array` asking for 2 entries from a 1-entry buffer — second
-- entry hits EOF.
#guard
  (Decodable.parseArray (α := RawRela) fixtureBytes 2).toOption.isNone

end Example

end LeanLoad.Parse

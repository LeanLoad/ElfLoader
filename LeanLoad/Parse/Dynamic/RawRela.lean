/-
gabi 06 § Relocation — `Elf64_Rela` entry (with explicit addend).

`r_addend` is stored as `UInt64`; per gabi 06 it is the bit pattern
of an `Elf64_Sxword` (signed). Signed interpretation happens at apply
time. We model only `Rela` (with addend); the `Rel` form is allowed
by gabi but neither AArch64 nor x86-64 emits it for dynamic
relocations.

Bit-field accessors `sym` / `type` (which unpack `r_info`) live in
`Elaborate/Reloc.lean` — they're interpretive, not byte-level decode.
-/

import LeanLoad.Parse.Decode
import LeanLoad.Parse.Deriving

namespace LeanLoad.Parse

/-- 64-bit relocation entry with explicit addend. -/
structure RawRela where
  r_offset : UInt64
  r_info   : UInt64
  r_addend : UInt64
  deriving Repr, Inhabited, BytesDecode

/-- Size of one `Elf64_Rela` on disk: 8+8+8 = 24. -/
def RawRelaSize : Nat := 24


/-- 24-byte rela-table fixture: one `R_X86_64_RELATIVE` relocation at
    offset `0x100`. The `r_offset` lies inside the consolidated
    fixture's PT_LOAD memsz, so `coversRela` accepts at elaborate
    time. `r_info = 8` packs `(sym << 32) | type` with `sym = 0` and
    `type = 8 = R_X86_64_RELATIVE`; non-zero `sym` cases (e.g.
    `R_X86_64_GLOB_DAT`) live in the per-arch reloc tables and tests
    in `Elaborate/Reloc.lean`. -/
def RawRela.fixtureBytes : ByteArray := ⟨#[
  0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- r_offset = 0x100
  0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- r_info   = 8 (sym=0, type=R_X86_64_RELATIVE)
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00    -- r_addend = 0
]⟩

#guard RawRela.fixtureBytes.size == RawRelaSize  -- = 24

section Example

open RawRela

private def parsedRelas : Option (Array RawRela) :=
  (Parser.run fixtureBytes (decodeArray (α := RawRela) 0 1)).toOption

#guard parsedRelas.map (·.size) = some 1
#guard (parsedRelas.bind (·[0]?)).map (·.r_offset) = some 0x100
#guard (parsedRelas.bind (·[0]?)).map (·.r_info)   = some 8       -- R_X86_64_RELATIVE
#guard (parsedRelas.bind (·[0]?)).map (·.r_addend) = some 0

-- ── Error cases ──────────────────────────────────────────────────────
-- Truncated rela: 15 bytes when 24 (RawRelaSize) expected — EOF inside
-- the `r_info` u64 read.
#guard
  (Parser.run (fixtureBytes.extract 0 15) (BytesDecode.decode : Parser RawRela)).toOption.isNone

-- `decodeArray` asking for 2 entries from a 1-entry buffer — second
-- entry hits EOF.
#guard
  (Parser.run fixtureBytes (decodeArray (α := RawRela) 0 2)).toOption.isNone

end Example

end LeanLoad.Parse

/-
Relocation entries — bytes only.

Spec: gabi 06 (`third_party/gabi/docsrc/elf/06-reloc.rst`).

`Elf64_Rela` packs symbol index and relocation type into `r_info`:

    sym  = r_info >> 32
    type = r_info & 0xffffffff

Type + byte-level parser. Per-arch relocation tables and the
`Formula` interpretation of `(type, S, A, B, P)` live in
`Elaborate.Reloc.{Aarch64, X86_64, Formula}`.

We model only `Rela` (with addend); the `Rel` form is allowed by
gabi but neither AArch64 nor x86-64 emits it for dynamic relocations.
-/

import LeanLoad.Parse.Bytes

namespace LeanLoad.Parse

/-- Raw 64-bit relocation entry. `r_addend` is stored as `UInt64`
    here; per gabi 06 it is the bit pattern of an `Elf64_Sxword`
    (signed). Signed interpretation happens at apply time. -/
structure RawRela where
  r_offset : UInt64
  r_info   : UInt64
  r_addend : UInt64
  deriving Repr, Inhabited

namespace RawRela

/-- Size of one `Elf64_Rela` on disk (gabi 06: 8+8+8 = 24). -/
def entrySize : Nat := 24

def sym (r : RawRela) : UInt32 := (r.r_info >>> 32).toUInt32
def type (r : RawRela) : UInt32 := (r.r_info &&& 0xffffffff).toUInt32

end RawRela

section Example
private def r : RawRela := { r_offset := 0xdead, r_info := 0x0000007b00000403, r_addend := 0 }
#guard r.sym  = 0x7b
#guard r.type = 0x403

#guard ({ r_offset := 0, r_info := 0,    r_addend := 0 } : RawRela).sym  = 0
#guard ({ r_offset := 0, r_info := 0,    r_addend := 0 } : RawRela).type = 0
#guard ({ r_offset := 0, r_info := 1027, r_addend := 0 } : RawRela).sym  = 0
#guard ({ r_offset := 0, r_info := 1027, r_addend := 0 } : RawRela).type = 1027
end Example

end LeanLoad.Parse

-- ============================================================================
-- Byte-level parser.
-- ============================================================================

namespace LeanLoad.Parse.Reloc

open LeanLoad.Parse
open LeanLoad.Parse.Bytes

def parseRela : Parser RawRela := do
  let r_offset ← u64le
  let r_info   ← u64le
  let r_addend ← u64le
  return { r_offset, r_info, r_addend }

/-- Parse `count` `Elf64_Rela` entries starting at `offset`. -/
def parseRelaTable (offset count : Nat) : Parser (Array RawRela) :=
  parseArray offset count parseRela

end LeanLoad.Parse.Reloc

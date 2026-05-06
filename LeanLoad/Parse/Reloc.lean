/-
Byte-level parsers for `Elf64_Rel` and `Elf64_Rela`.
Spec types live in `LeanLoad.Spec.Reloc`.
-/

import LeanLoad.Parse.Bytes
import LeanLoad.Spec.Reloc

namespace LeanLoad.Parse.Reloc

open LeanLoad.Parse.Bytes
open LeanLoad.Spec.Reloc

def parseRela : Parser Rela64 := do
  let r_offset ← u64le
  let r_info   ← u64le
  let r_addend ← u64le
  return { r_offset, r_info, r_addend }

/-- Parse `count` `Elf64_Rela` entries starting at `offset`. -/
def parseRelaTable (offset count : Nat) : Parser (Array Rela64) :=
  parseArray offset count parseRela

end LeanLoad.Parse.Reloc

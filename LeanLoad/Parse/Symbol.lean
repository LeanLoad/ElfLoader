/-
Byte-level parser for symbol-table entries.
Spec types live in `LeanLoad.Spec.Symbol`.
-/

import LeanLoad.Parse.Bytes
import LeanLoad.Spec.Symbol

namespace LeanLoad.Parse.Symbol

open LeanLoad.Parse.Bytes
open LeanLoad.Spec.Symbol

/-- Parse one symbol entry at the current cursor. -/
def parse : Parser Symbol64 := do
  let st_name  ← u32le
  let st_info  ← u8
  let st_other ← u8
  let st_shndx ← u16le
  let st_value ← u64le
  let st_size  ← u64le
  return { st_name, st_info, st_other, st_shndx, st_value, st_size }

/-- Parse `count` consecutive symbol entries starting at `offset`. -/
def parseTable (offset count : Nat) : Parser (Array Symbol64) :=
  parseArray offset count parse

end LeanLoad.Parse.Symbol

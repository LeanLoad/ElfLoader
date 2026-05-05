/-
Byte-level parser for program-header entries.
Spec types live in `LeanLoad.Spec.Program`.
-/

import LeanLoad.Parse.Bytes
import LeanLoad.Spec.Program

namespace LeanLoad.Parse.Program

open LeanLoad.Parse.Bytes
open LeanLoad.Spec.Program

/-- Parse one program header entry at the current cursor. -/
def parse : Parser Header64 := do
  let p_type   ← u32le
  let p_flags  ← u32le
  let p_offset ← u64le
  let p_vaddr  ← u64le
  let p_paddr  ← u64le
  let p_filesz ← u64le
  let p_memsz  ← u64le
  let p_align  ← u64le
  return { p_type, p_flags, p_offset, p_vaddr, p_paddr, p_filesz, p_memsz, p_align }

/-- Parse `count` consecutive program-header entries starting at `offset`. -/
def parseTable (offset count : Nat) : Parser (Array Header64) :=
  parseArray offset count parse

end LeanLoad.Parse.Program

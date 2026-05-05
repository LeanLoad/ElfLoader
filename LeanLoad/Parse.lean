/-
`LeanLoad.Parse` — pure ELF parsing.

Each sub-module corresponds to one gabi chapter; `Bytes` provides the
parser monad and primitives that the others build on.
-/

import LeanLoad.Parse.Bytes
import LeanLoad.Parse.Header
import LeanLoad.Parse.Program
import LeanLoad.Parse.Dynamic
import LeanLoad.Parse.Symbol
import LeanLoad.Parse.Reloc
import LeanLoad.Parse.File

-- ============================================================================
-- Tests. Each `Test.run path : IO Nat` returns the failure count; the
-- runner in `LeanLoad/Test.lean` aggregates these.
-- ============================================================================
namespace LeanLoad.Parse.Test

/-- End-to-end smoke test: parse the given bytes and assert basics. -/
def run (bytes : ByteArray) : IO Nat := do
  let mut failures := 0

  match Parser.run bytes Header.parse with
  | .error e =>
      IO.eprintln s!"Header.parse failed: {e}"
      failures := failures + 1
  | .ok h =>
      if h.e_type != Header.ET_DYN then
        IO.eprintln s!"e_type: expected ET_DYN={Header.ET_DYN}, got {h.e_type}"
        failures := failures + 1
      if h.e_ehsize != 64 then
        IO.eprintln s!"e_ehsize: expected 64, got {h.e_ehsize}"
        failures := failures + 1
      if h.e_phentsize != 56 then
        IO.eprintln s!"e_phentsize: expected 56, got {h.e_phentsize}"
        failures := failures + 1
      match Parser.run bytes (Program.parseTable h.e_phoff.toNat h.e_phnum.toNat) with
      | .error e =>
          IO.eprintln s!"Program.parseTable failed: {e}"
          failures := failures + 1
      | .ok phs =>
          if phs.size != h.e_phnum.toNat then
            IO.eprintln s!"phnum mismatch: header says {h.e_phnum}, parsed {phs.size}"
            failures := failures + 1

  match File.parse bytes with
  | .error e =>
      IO.eprintln s!"File.parse failed: {e}"
      failures := failures + 1
  | .ok elf =>
      if elf.needed.size < 3 then
        IO.eprintln s!"expected ≥ 3 NEEDED entries, got {elf.needed.size}: {elf.needed}"
        failures := failures + 1
      if !elf.needed.any (· == "libfoo.so") then
        IO.eprintln s!"libfoo.so not in NEEDED: {elf.needed}"
        failures := failures + 1
      if !elf.needed.any (· == "libbar.so") then
        IO.eprintln s!"libbar.so not in NEEDED: {elf.needed}"
        failures := failures + 1
      if elf.runpath.isNone then
        IO.eprintln "expected DT_RUNPATH set"
        failures := failures + 1
  return failures

end LeanLoad.Parse.Test

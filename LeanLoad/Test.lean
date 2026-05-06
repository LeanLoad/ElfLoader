/-
Entry point for `lean_exe test`. Per-module test bodies live next
to their impl (`LeanLoad.X.Test.run`); this driver does the build
fixture's existence check, reads bytes once, runs `discover` once,
then dispatches to each suite with the prepared inputs.
-/
import LeanLoad

open LeanLoad

def main : IO UInt32 := do
  let path := "build/main"
  unless ← System.FilePath.pathExists path do
    IO.eprintln s!"skip: {path} not built"
    return 0
  let bytes ← IO.FS.readBinFile path
  let lm    ← Discover.discover path
  -- Reloc is parametric over the per-arch formula. Pick by `e_machine`
  -- so the suite runs against whichever arch the fixture was built for.
  let some main := lm.main?
    | do IO.eprintln "skip: empty link map"; return 0
  let some formula := Spec.Reloc.formulaFor main.elf.header.e_machine
    | do IO.eprintln s!"skip: unsupported e_machine={main.elf.header.e_machine}"; return 0
  let suites : List (String × IO Nat) := [
    ("Parse",    Parse.Test.run bytes),
    ("Discover", Discover.Test.run lm),
    ("Resolve",  Resolve.Test.run lm),
    ("Layout",   Layout.Test.run lm),
    ("Reloc",    Reloc.Test.run formula lm)
  ]
  let mut failures : Nat := 0
  for (name, suite) in suites do
    let f ← suite
    if f = 0 then
      IO.println s!"  ok    {name}"
    else
      IO.println s!"  FAIL  {name} ({f})"
      failures := failures + f
  if failures = 0 then
    IO.println "all tests passed"
    return 0
  else
    IO.eprintln s!"{failures} test(s) failed"
    return 1

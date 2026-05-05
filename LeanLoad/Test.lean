/-
Entry point for `lean_exe test`. Per-module test bodies live next
to their impl (`LeanLoad.X.Test.run`); this driver does the build
fixture's existence check, reads bytes once, runs `discover` once,
then dispatches to each suite with the prepared inputs.
-/
import LeanLoad

def main : IO UInt32 := do
  let path := "build/main"
  unless ← System.FilePath.pathExists path do
    IO.eprintln s!"skip: {path} not built"
    return 0
  let bytes ← IO.FS.readBinFile path
  let lm    ← LeanLoad.Discover.discover path
  let suites : List (String × IO Nat) := [
    ("Parse",    LeanLoad.Parse.Test.run bytes),
    ("Discover", LeanLoad.Discover.Test.run lm),
    ("Resolve",  LeanLoad.Plan.Resolve.Test.run lm),
    ("Init",     LeanLoad.Plan.Init.Test.run lm),
    ("Reloc",    LeanLoad.Plan.Reloc.Test.run lm)
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

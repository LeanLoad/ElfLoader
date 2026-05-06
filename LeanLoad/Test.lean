/-
Integration test entry for `lean_exe test`.

Drives Parse / Discover / Resolve / Layout / Reloc / Map / Apply
against the real `build/main` fixture. Exec is deferred to `./run.sh`:
its constructor calls are user-supplied (observable as the loaded
program's printf in E2E output) and the entry transfer doesn't
return, so it would terminate the test process.

Each stage's runner lives in its own file (`X.test`) and is
self-contained: IO stages re-run their upstream setup (extra mmaps
that persist for the process lifetime — negligible for our
fixtures; the trade-off is each row failing independently).

Layering:

  - `#guard` blocks (in impl files, fixtures from `Fixtures.lean`)
      — unit-level invariants, evaluated at elaboration.
  - `lake test` (this file) — integration on the real fixture.
  - `./run.sh` — end-to-end including Exec.
-/
import LeanLoad

open LeanLoad

def main : IO UInt32 := do
  let path := "build/main"
  unless ← System.FilePath.pathExists path do
    IO.eprintln s!"skip: {path} not built"
    return 0
  let g     ← Discover.discover path
  let some main := g.main?
    | do IO.eprintln "skip: empty link map"; return 0
  let some formula := Spec.Reloc.formulaFor main.elf.header.e_machine
    | do IO.eprintln s!"skip: unsupported e_machine={main.elf.header.e_machine}"; return 0
  let some mainHandle := main.handle
    | do IO.eprintln "skip: main has no file handle"; return 0

  let layouts := g.layouts
  let rt      := Resolve.buildTable g

  let suites : List (String × IO Nat) := [
    ("Parse",    Parse.File.test mainHandle),
    ("Discover", Discover.test g),
    ("Resolve",  Resolve.test g),
    ("Layout",   Layout.test g),
    ("Order",    Order.test g),
    ("Reloc",    Reloc.test formula g),
    ("Map",      Map.test g layouts),
    ("Apply",    Apply.test g layouts formula rt)
  ]

  let mut failures : Nat := 0
  for (name, suite) in suites do
    let f ← suite
    if f = 0 then IO.println s!"  ok    {name}"
    else IO.println s!"  FAIL  {name} ({f})"
    failures := failures + f

  -- Exec is intentionally NOT exercised here — its entry transfer
  -- doesn't return. ./run.sh covers it as the E2E layer.

  if failures = 0 then
    IO.println "all tests passed"
    return 0
  else
    IO.eprintln s!"{failures} test(s) failed"
    return 1

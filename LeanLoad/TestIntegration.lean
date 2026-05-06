/-
Integration test entry for `lean_exe test`.

Drives every stage in the pipeline against the real `build/main`
fixture **except the final Exec** (transfer of control), which would
terminate this test process. Per-stage:

  - Parse / Discover / Resolve / Layout / Reloc — delegate to the
    `X.Test.run` runners colocated with each impl.
  - Map / Apply / Init — exercised inline below; we assert the
    structural results (bases shape, no IO error, runInits returns).

The pure `#guard`s scattered through impl files cover unit-level
invariants; this file is the integration layer; `./run.sh` runs the
full E2E including Exec.
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

  let some main := lm.main?
    | do IO.eprintln "skip: empty link map"; return 0
  let some formula := Spec.Reloc.formulaFor main.elf.header.e_machine
    | do IO.eprintln s!"skip: unsupported e_machine={main.elf.header.e_machine}"; return 0

  let mut failures : Nat := 0

  -- Per-stage runners for the pure pipeline (Reloc here is the
  -- planning-side check; the IO apply happens further down).
  let suites : List (String × IO Nat) := [
    ("Parse",    Parse.Test.run bytes),
    ("Discover", Discover.Test.run lm),
    ("Resolve",  Resolve.Test.run lm),
    ("Layout",   Layout.Test.run lm),
    ("Reloc",    Reloc.Test.run formula lm)
  ]
  for (name, suite) in suites do
    let f ← suite
    if f = 0 then
      IO.println s!"  ok    {name}"
    else
      IO.println s!"  FAIL  {name} ({f})"
      failures := failures + f

  -- IO stages: Map → Apply → Init. Stop short of Exec, which would
  -- terminate this test process via the transfer-of-control path.
  let plan := Layout.fromLinkMap lm (Layout.initOrder lm) (Layout.finiOrder lm)
  let rt   := Resolve.buildTable lm

  try
    -- Map: every object gets a region array + chosen base. The
    -- shape should match the link map exactly.
    let (allRegions, bases) ← Load.mapAll lm plan
    if bases.size != lm.objects.size then
      IO.eprintln s!"Map: bases.size {bases.size} ≠ object count {lm.objects.size}"
      failures := failures + 1
    else if allRegions.size != lm.objects.size then
      IO.eprintln s!"Map: allRegions.size {allRegions.size} ≠ object count"
      failures := failures + 1
    else
      IO.println s!"  ok    Map ({bases.size} bases)"

    -- Apply: poke the planned reloc writes into mmap'd memory.
    -- Assertion: completes without raising.
    let writes := Reloc.plan formula lm bases rt
    Load.applyAllRelocs allRegions bases writes
    IO.println s!"  ok    Apply ({writes.size} writes)"

    -- Init: invoke each object's DT_INIT_ARRAY in dependency order.
    -- The ctors print to stdout (loaded program's libc); we just
    -- assert that `runInits` returned cleanly.
    Load.runInits lm bases plan
    IO.println "  ok    Init"
  catch e =>
    IO.eprintln s!"  FAIL  IO-stage exception: {e}"
    failures := failures + 1

  -- Exec is intentionally NOT exercised here — it doesn't return.
  -- ./run.sh covers it as the E2E layer.

  if failures = 0 then
    IO.println "all tests passed"
    return 0
  else
    IO.eprintln s!"{failures} test(s) failed"
    return 1

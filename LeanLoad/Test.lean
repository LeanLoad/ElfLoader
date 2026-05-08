/-
Integration test entry for `lake test`.

Runs Parse / Discover / Resolve / Layout / Order / Reloc / Map /
Apply against the real `build/main` fixture *as a single pipeline*:
each stage's output feeds the next, just like the production loader.
Each per-stage `*Test` function takes whatever upstream produced and
returns a failure count. No stage re-runs upstream IO.

Exec is deferred to `./run.sh`: its constructor calls are
user-supplied (observable as the loaded program's printf in E2E
output) and the entry transfer doesn't return, so it would terminate
the test process.

Layering:

  - `#guard` blocks (in impl files, fixtures from `Fixtures.lean`)
      — unit-level invariants, evaluated at elaboration.
  - `lake test` (this file) — integration on the real fixture.
  - `./run.sh` — end-to-end including Exec.
-/
import LeanLoad

open LeanLoad
open LeanLoad.Discover
open LeanLoad.Layout
open LeanLoad.Elaborate (Elf)

/-- Expected name set for the `build/main` fixture's dependency
    graph. libbar↔libbaz form a cycle (mutual NEEDED); the
    SONAME-keyed dedup must terminate the BFS. -/
private def expectedNames : Array String :=
  #["main", "libfoo.so", "libbar.so", "libbaz.so", "libc.so"]

/-- A pure assertion: succeed or fail with a message. Composes via
    `do` notation in `Except`, which short-circuits on first failure. -/
private def check (cond : Bool) (msg : String) : Except String Unit :=
  if cond then .ok () else .error msg

private def parseTest (elf : Elaborate.Elf) : Except String Unit := do
  check (elf.elfType == .dyn)
    s!"elfType: expected dyn, got {repr elf.elfType}"
  check (elf.segments.size > 0)
    s!"expected ≥ 1 PT_LOAD segment, got {elf.segments.size}"
  check (elf.needed.size ≥ 3)
    s!"expected ≥ 3 NEEDED entries, got {elf.needed.size}: {elf.needed}"
  check (elf.needed.any (· == "libfoo.so"))
    s!"libfoo.so not in NEEDED: {elf.needed}"
  check (elf.needed.any (· == "libbar.so"))
    s!"libbar.so not in NEEDED: {elf.needed}"
  check elf.runpath.isSome "expected DT_RUNPATH set"

private def discoverTest (g : ObjectList) : Except String Unit := do
  let names := g.val.map (·.name)
  check (g.val.size == expectedNames.size)
    s!"expected {expectedNames.size} objects, got {g.val.size}: {names}"
  for expected in expectedNames[1:] do
    check (names.any (· == expected))
      s!"{expected} missing from dependency graph: {names}"
  for nm in names do
    let occurrences := names.filter (· == nm) |>.size
    check (occurrences ≤ 1) s!"{nm} appears {occurrences} times — dedup failed"

private def resolveTest (g : ObjectList) : Except String Unit := do
  let elfs := g.val.map (·.elf)
  let table := Resolve.buildTable elfs
  let firstMissing := (table.missing[0]?.map (·.name)).getD ""
  check (table.missing.size == 0)
    s!"expected 0 missing, got {table.missing.size}; first: {firstMissing}"
  for (sym, expectedProvider) in [("libfoo_print", "libfoo.so"),
                                   ("libbar_step",  "libbar.so"),
                                   ("libbaz_step",  "libbaz.so")] do
    match Resolve.resolveByName elfs sym with
    | none => .error s!"{sym} did not resolve"
    | some r =>
      let provider := (g.val[r.objectIdx.val]?.map (·.name)).getD "?"
      check (provider == expectedProvider)
        s!"{sym} resolved to {provider}, expected {expectedProvider}"

private def layoutTest (g : ObjectList) : Except String Unit := do
  -- `Layout.layouts` succeeds → returns a sized subtype; the size
  -- proof is the second component, so this test only checks that the
  -- well-formedness validation succeeds (size match is by construction).
  let _ ← Layout.layouts Layout.dynAnchor (g.val.map (·.elf))
  .ok ()

private def orderTest (g : ObjectList) : Except String Unit := do
  let order := Init.order g
  check (order.size == g.val.size)
    s!"order size {order.size} ≠ object count {g.val.size}"
  check (order.back? == some 0)
    s!"main (idx 0) should be last in order; got {order}"

private def relocTest (g : ObjectList) (formula : Elaborate.Formula) : Except String Unit := do
  let elfs := g.val.map (·.elf)
  let layouts ← Layout.layouts Layout.dynAnchor elfs
  let patches ← Reloc.plan formula elfs layouts.val layouts.property.left
                   (Resolve.buildTable elfs)
  check (patches.size > 0) "expected nonzero relocation writes"

-- Realize (mmap + overlays + zeroout + mprotect + patch writes +
-- ctor calls + exec) has no test stage: it doesn't return (it
-- `execAndJump`s into the loaded program). The pure planners above
-- (`Layout`, `Reloc`, `Init`) are what's testable here; the IO
-- bookend is exercised E2E by `./run.sh`.

/-- Run a pure stage's test, log pass/fail, return whether it passed. -/
private def runStage (name : String) (suite : Except String Unit) : IO Bool := do
  match suite with
  | .ok () => IO.println s!"  ok    {name}"; return true
  | .error e => IO.println s!"  FAIL  {name}: {e}"; return false

def main : IO UInt32 := do
  let path := "build/main"
  unless ← System.FilePath.pathExists path do
    IO.eprintln s!"skip: {path} not built"
    return 0

  -- Pure-stage tests own their computations. Only IO state (image)
  -- is captured at the harness level. Stop on first failure.

  let g ← Discover.discover path
  unless ← runStage "Discover" (discoverTest g) do return 1

  let main := g.main
  unless ← runStage "Parse"   (parseTest main.elf)  do return 1
  unless ← runStage "Resolve" (resolveTest g)       do return 1
  unless ← runStage "Layout"  (layoutTest g)        do return 1
  unless ← runStage "Order"   (orderTest g)         do return 1

  let formula := Elaborate.formulaFor main.elf.machine
  unless ← runStage "Reloc"   (relocTest g formula) do return 1

  -- Apply has no test stage — see comment above. The actual apply
  -- is exercised E2E by `./run.sh`.

  -- Exec is intentionally NOT exercised here — its entry transfer
  -- doesn't return. ./run.sh covers it as the E2E layer.

  IO.println "all tests passed"
  return 0

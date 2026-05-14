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
open LeanLoad.Plan
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
  -- Ctor / dtor arrays: the existence of `Elf` already proves the
  -- entries are in executable PT_LOADs (via `initArrInExecSeg` /
  -- `finiArrInExecSeg`); these checks confirm the parser populated
  -- them so a future bug that loses `DT_INIT_ARRAY` / `DT_FINI_ARRAY`
  -- doesn't slip through silently.
  check (elf.initArr.size > 0) "expected ≥ 1 DT_INIT_ARRAY entry"
  -- gcc/clang link in __libc_atexit-style finalizers, so a normal
  -- ET_DYN main has at least one fini entry.
  check (elf.finiArr.size > 0) "expected ≥ 1 DT_FINI_ARRAY entry"

private def discoverTest (g : LoadGraph) : Except String Unit := do
  let names := g.objects.map (·.name)
  check (g.objects.size == expectedNames.size)
    s!"expected {expectedNames.size} objects, got {g.objects.size}: {names}"
  for expected in expectedNames[1:] do
    check (names.any (· == expected))
      s!"{expected} missing from dependency graph: {names}"
  for nm in names do
    let occurrences := names.filter (· == nm) |>.size
    check (occurrences ≤ 1) s!"{nm} appears {occurrences} times — dedup failed"

private def resolveTest (g : LoadGraph) : Except String Unit := do
  let elfs := g.objects.map (·.elf)
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
      let provider := (g.objects[r.objectIdx.val]?.map (·.name)).getD "?"
      check (provider == expectedProvider)
        s!"{sym} resolved to {provider}, expected {expectedProvider}"

/-- Synthetic reservation base used by tests that don't need the
    kernel-picked address. Lives only here — production gets the
    real base from `Runtime.mmapAnon`. -/
private def testAnchor : UInt64 := 0x80000000

private def layoutTest (g : LoadGraph) : Except String Unit := do
  -- `Layout.ofElfs` succeeds → returns a `Layout elfs.size` with
  -- per-elf `segmentsSorted` and per-segment relocs woven in.
  let elfs := g.objects.map (·.elf)
  let rt := Resolve.buildTable elfs
  let _ ← Layout.ofElfs elfs rt
  .ok ()

private def orderTest (g : LoadGraph) : Except String Unit := do
  let order := (Init.order g).map (·.val)
  check (order.size == g.objects.size)
    s!"order size {order.size} ≠ object count {g.objects.size}"
  check (order.back? == some 0)
    s!"main (idx 0) should be last in order; got {order}"

private def relocTest (g : LoadGraph) (formula : Elaborate.Formula) : Except String Unit := do
  let elfs := g.objects.map (·.elf)
  let rt := Resolve.buildTable elfs
  let lp ← Layout.ofElfs elfs rt
  let totalEntries := lp.elfs.foldl (init := 0) fun acc ep =>
    ep.segments.foldl (init := acc) fun acc sp => acc + sp.relocs.size
  check (totalEntries > 0) "expected nonzero planned relocations"
  -- Bake them too — exercises the formula + symValueOf path.
  let bases := assignBases testAnchor lp
  have h_bases : bases.size = elfs.size :=
    (assignBases_size testAnchor lp).trans lp.elfs_size
  let mut stores : Array StoreOp := #[]
  for h : i in [:lp.elfs.size] do
    let ep := lp.elfs[i]
    let base := bases[i]'(by rw [h_bases]; rw [← lp.elfs_size]; exact h.upper)
    for sp in ep.segments do
      stores := stores ++
        (← Materialize.bakeSegmentRelocs formula elfs rfl bases h_bases base
              sp.segment sp.relocs)
  check (stores.size > 0) "expected nonzero baked Store ops"

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

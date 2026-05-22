/-
Discover behavior tests — pure, in-memory, no IO.

The DFS driver (`dfs`, `discoverWith` in `Discover.Driver`) is
generic over the effect monad. This file substitutes an in-memory
`TestStore` for the filesystem, builds an `Effects (Except String)`
instance over it (re-simulating the C-side path search at the Lean
level), and exercises shape-level behaviors via `#guard` at
elaboration time:

  · Linear chain (4 objects in DFS pre-order).
  · Diamond (shared dep loaded once, two in-edges, DFS pre-order).
  · Cycle (A → B → A terminates without diverging — back-edge
    dedups against the in-progress ancestor's idx).
  · Missing dep (returns `Except.error`).
  · Search-order precedence (env > runpath).

These are unit-level checks. The integration path (real ELFs on disk
via `Runtime.openByName`) is exercised by `LeanLoad.Test`'s
`discoverTest` over `build/main`.

Canonical name = `elf.soname` (required) for NEEDED deps; `basename
mainPath` for the main entry. Matches production `Effects.io` /
`discover` exactly. `mockElf` defaults `soname := some "anon"` so the
SONAME-required production policy is satisfied by default — tests
that want to exercise the SONAME-missing error path pass
`soname := none` explicitly.
-/

import LeanLoad.Discover.Driver

namespace LeanLoad.Discover

open LeanLoad
open LeanLoad.Parse (Elf)

-- ============================================================================
-- Minimal Elf builder — only the fields BFS reads (`soname`, `runpath`,
-- `needed`) are interesting. Everything else gets a trivial value; the
-- segment / init / fini invariants discharge by `decide` on empty arrays.
-- ============================================================================

/-- Build a minimal `Elf` for Discover testing. `soname`, `runpath`,
    and `needed` are the only fields BFS observes; everything else is
    zeroed and the structural invariants discharge automatically.
    `soname` defaults to `some "anon"` because production `Effects.io`
    *requires* DT_SONAME on every NEEDED-loaded `.so`. Tests that want
    to exercise the SONAME-missing error path can pass `soname := none`
    explicitly. -/
def mockElf (soname : Option String := some "anon")
    (runpath : Option String := none)
    (needed : Array String := #[]) : Elf := {
  header   := { (default : Parse.Ehdr) with
    e_type := .dyn
    e_machine := .x86_64
    e_entry := 0
    e_phoff := 0
    e_phnum := 0 }
  symtab   := #[]
  needed
  soname
  runpath
  segments := Parse.Segments.empty
  initArr  := #[]
  finiArr  := #[] }

-- ============================================================================
-- TestStore — in-memory `path → Elf` map. Mirrors what the production
-- C runtime's `leanload_open_by_name` searches, but in Lean. The
-- `searchCandidates` simulator below is test-only — production path
-- resolution happens entirely in C.
-- ============================================================================

/-- A `path → Elf` map for tests. Simple `List` for legibility — tests
    are 3-5 entries each. -/
abbrev TestStore := List (String × Elf)

namespace TestStore

/-- Look up an entry by path. -/
def getElf? (store : TestStore) (path : String) : Option Elf :=
  (store.find? (·.fst == path)).map (·.snd)

end TestStore

/-- Mirror the C runtime's path search at the Lean level. Test-only —
    production goes through `Runtime.openByName`. -/
private def testSearchCandidates (soname : String)
    (runpath : Option String) (envPath : Option String) : Array String :=
  if soname.contains '/' then #[soname]
  else
    let parsePathList (s : String) : Array String :=
      s.splitOn ":" |>.filter (! ·.isEmpty) |>.toArray
    let dirs : Array String := Id.run do
      let mut acc : Array String := #[]
      if let some p := envPath then acc := acc ++ parsePathList p
      if let some p := runpath then acc := acc ++ parsePathList p
      return acc
    dirs.map (fun d => s!"{d}/{soname}")

/-- The test `Effects` instance: simulate `Runtime.openByName` over a
    `TestStore`, with the same SONAME-required policy as production
    `Effects.io` — `findSome?` skips entries whose elf has no DT_SONAME
    (treats them as "not found"; production throws). Closure captures
    both the store and a simulated `LD_LIBRARY_PATH`. -/
def Effects.test (store : TestStore) (envPath : Option String := none) :
    Effects (Except String) :=
  { resolveDep := fun soname runpath => .ok <|
      (testSearchCandidates soname runpath envPath).findSome? fun path =>
        (store.getElf? path).bind fun elf =>
          elf.soname.map fun name => (name, (default : Runtime.File), elf)
    fail := fun {_} msg => .error msg }

-- ============================================================================
-- discoverPure — the test-side counterpart to `discover`. Takes the
-- in-memory store, the main object's path, and (optionally) a simulated
-- envPath, and runs the BFS to completion in `Except String`.
-- ============================================================================

/-- Run the DFS to completion against a `TestStore`. The main object
    is looked up directly by path (no soname search for it — same as
    production `discover`). Main's canonical name is `basename
    mainPath` (via `LoadedObject.ofMain`, same as production). -/
def discoverPure (store : TestStore) (mainPath : String)
    (envPath : Option String := none) : Except String LoadGraph := do
  let some mainElf := store.getElf? mainPath
    | .error s!"discoverPure: main {mainPath} not in store"
  discoverWith (Effects.test store envPath) 64
    (LoadedObject.ofMain mainPath (default : Runtime.File) mainElf)

-- ============================================================================
-- Behavior tests via `#guard`. Each scenario builds a small store, runs
-- discoverPure, and asserts properties of the resulting LoadGraph.
-- ============================================================================

-- Test paths starting with `/` short-circuit search to a literal
-- lookup, keeping the shape tests independent of search-context details.

-- ---- 1. Linear chain ----------------------------------------------------
-- /main → /b → /c → /d. Each elf needs the next one only.

private def linearStore : TestStore := [
  ("/main", mockElf (soname := some "main") (needed := #["/b"])),
  ("/b",    mockElf (soname := some "b")    (needed := #["/c"])),
  ("/c",    mockElf (soname := some "c")    (needed := #["/d"])),
  ("/d",    mockElf (soname := some "d"))]

private def linearGraph : Except String LoadGraph := discoverPure linearStore "/main"

#guard match linearGraph with
  | .ok g => g.objects.size = 4
  | _     => false

#guard match linearGraph with
  | .ok g => (g.objects.map (·.name)) = #["main", "b", "c", "d"]
  | _     => false

-- main → b → c → d: each row depends only on the next.
#guard match linearGraph with
  | .ok g => g.deps = #[#[1], #[2], #[3], #[]]
  | _     => false

-- ---- 2. Diamond ---------------------------------------------------------
-- /main → {/b, /c}; /b → /d; /c → /d. Shared dep `/d` should load once.

private def diamondStore : TestStore := [
  ("/main", mockElf (soname := some "main") (needed := #["/b", "/c"])),
  ("/b",    mockElf (soname := some "b")    (needed := #["/d"])),
  ("/c",    mockElf (soname := some "c")    (needed := #["/d"])),
  ("/d",    mockElf (soname := some "d"))]

private def diamondGraph : Except String LoadGraph := discoverPure diamondStore "/main"

-- `/d` appears once, four objects total.
#guard match diamondGraph with
  | .ok g => g.objects.size = 4
  | _     => false

-- DFS pre-order: main (0), then descend into /b — push b (1), descend
-- into /d — push d (2), back up to /c — push c (3). `/c → /d` resolves
-- as a dedup hit against d at idx 2.
#guard match diamondGraph with
  | .ok g => (g.objects.map (·.name)) = #["main", "b", "d", "c"]
  | _     => false

-- main (0) → {b (1), c (3)}; b (1) → d (2); d (2) → ∅; c (3) → d (2).
-- The shared dep `/d` is loaded once at idx 2; both b and c record
-- an edge to it (c's edge via the dedup-hit branch in `dfs`).
#guard match diamondGraph with
  | .ok g => g.deps = #[#[1, 3], #[2], #[], #[2]]
  | _     => false

-- ---- 3. Cycle -----------------------------------------------------------
-- /main → /b → /main. The dedup check via `findLoadedIdx` short-circuits
-- the second visit through the `.skip` branch — terminates cleanly.

private def cycleStore : TestStore := [
  ("/main", mockElf (soname := some "main") (needed := #["/b"])),
  ("/b",    mockElf (soname := some "b")    (needed := #["/main"]))]

private def cycleGraph : Except String LoadGraph := discoverPure cycleStore "/main"

#guard match cycleGraph with
  | .ok g => g.objects.size = 2
  | _     => false

-- main depends on b; b depends back on main (the .skip branch records
-- this edge without re-loading main).
#guard match cycleGraph with
  | .ok g => g.deps = #[#[1], #[0]]
  | _     => false

-- ---- 4. SONAME-based dedup ---------------------------------------------
-- main NEEDs both `/libfoo.so` and `/libfoo.so.1` — two different files
-- in the store, but BOTH have `DT_SONAME = "libfoo.so.1"`. Production
-- policy: dedup by SONAME. The second resolution hits the post-load
-- dedup branch in `BfsState.step.resolve` via `findLoadedIdx`.

private def sonameStore : TestStore := [
  ("/main",        mockElf (soname := some "main")
                            (needed := #["/libfoo.so", "/libfoo.so.1"])),
  ("/libfoo.so",   mockElf (soname := some "libfoo.so.1")),
  ("/libfoo.so.1", mockElf (soname := some "libfoo.so.1"))]

private def sonameGraph : Except String LoadGraph := discoverPure sonameStore "/main"

-- Two objects loaded (main + one libfoo); the second NEEDED dedups by SONAME.
#guard match sonameGraph with
  | .ok g => g.objects.size = 2
  | _     => false

#guard match sonameGraph with
  | .ok g => (g.objects.map (·.name)) = #["main", "libfoo.so.1"]
  | _     => false

-- main has two edges to libfoo (one per NEEDED entry), both to idx 1.
#guard match sonameGraph with
  | .ok g => g.deps = #[#[1, 1], #[]]
  | _     => false

-- ---- 5. Missing dep -----------------------------------------------------
-- main NEEDs /missing which isn't in the store → resolveDep returns
-- none → BfsState.step fires `eff.fail` → `.error` propagates out.

private def missingStore : TestStore := [
  ("/main", mockElf (soname := some "main") (needed := #["/missing"]))]

#guard (discoverPure missingStore "/main").isOk = false

-- ---- 6. Search-order precedence -----------------------------------------
-- env > runpath. The same bare soname `libx.so` exists in both
-- `/env/libx.so` and `/run/libx.so`; with envPath=`/env`, env wins.

private def searchStore : TestStore := [
  ("/main",         mockElf (soname := some "main") (runpath := some "/run")
                             (needed := #["libx.so"])),
  ("/env/libx.so",  mockElf (soname := some "libx-from-env")),
  ("/run/libx.so",  mockElf (soname := some "libx-from-run"))]

#guard match discoverPure searchStore "/main" (envPath := some "/env") with
  | .ok g => (g.objects.map (·.name)) = #["main", "libx-from-env"]
  | _     => false

-- Without envPath, runpath wins.
#guard match discoverPure searchStore "/main" (envPath := none) with
  | .ok g => (g.objects.map (·.name)) = #["main", "libx-from-run"]
  | _     => false

-- ---- 7. SONAME-required for NEEDED deps --------------------------------
-- A NEEDED dep without DT_SONAME is rejected: production Effects.io
-- throws; Effects.test (matching policy) makes the entry invisible to
-- the store lookup (findSome? skips SONAME-less elves), surfacing as
-- the same "cannot find" diagnostic.

private def sonameMissingStore : TestStore := [
  ("/main",          mockElf (soname := some "main") (needed := #["/anonlib"])),
  ("/anonlib",       mockElf (soname := none))]    -- SONAME-less .so

#guard (discoverPure sonameMissingStore "/main").isOk = false

-- Main without SONAME is fine — main's canonical name is basename
-- mainPath, never elf.soname. Loads cleanly with no deps.
private def mainNoSonameStore : TestStore := [
  ("/main", mockElf (soname := none))]

#guard match discoverPure mainNoSonameStore "/main" with
  | .ok g => g.objects.size = 1 ∧ g.main.name = "main"
  | _     => false

end LeanLoad.Discover

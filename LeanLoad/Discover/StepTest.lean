/-
Discover behavior tests — pure, in-memory, no IO.

The BFS state machine (`bfsStep1`, `discoverLoopWith`) is generic over
the effect monad. This file substitutes an in-memory `TestStore` for
the filesystem, builds an `Effects (Except String)` instance over it,
and exercises shape-level behaviors via `#guard` at elaboration time:

  · Linear chain (4 objects in BFS order).
  · Diamond (shared dep loaded once, two in-edges).
  · Cycle (A → B → A terminates without diverging).
  · Canonical-name dedup (DT_NEEDED libfoo.so → DT_SONAME libfoo.so.1).
  · Missing dep (returns `Except.error`).
  · Search-order precedence (env > runpath > defaults).

These are unit-level checks. The integration path (real ELFs on disk)
is still exercised by `LeanLoad.Test`'s `discoverTest`.
-/

import LeanLoad.Discover.Step

namespace LeanLoad.Discover

open LeanLoad
open LeanLoad.Elaborate (Elf)

-- ============================================================================
-- Minimal Elf builder — only the fields BFS reads (`soname`, `runpath`,
-- `needed`) are interesting. Everything else gets a trivial value; the
-- segment / init / fini invariants discharge by `decide` on empty arrays.
-- ============================================================================

/-- Build a minimal `Elf` for Discover testing. `soname`, `runpath`,
    and `needed` are the only fields BFS observes; everything else is
    zeroed and the structural invariants discharge automatically. -/
def mockElf (soname : Option String := none) (runpath : Option String := none)
    (needed : Array String := #[]) : Elf := {
  elfType  := .dyn
  machine  := .x86_64
  entry    := 0
  phoff    := 0
  phnum    := 0
  symtab   := #[]
  needed
  soname
  runpath
  initArr  := #[]
  finiArr  := #[]
  segments := #[]
  segmentsSorted     := by decide
  segmentsNonOverlap := by decide
  phdrCovered        := by decide
  initArrInExecSeg   := by decide
  finiArrInExecSeg   := by decide }

-- ============================================================================
-- TestStore — in-memory `path → Elf` map. Mirrors the filesystem
-- abstraction the production `Effects.io` uses: `resolveDep` enumerates
-- candidate paths via `searchCandidates`, then looks each one up.
-- ============================================================================

/-- A `path → Elf` map for tests. Simple `List` for legibility — tests
    are 3-5 entries each. -/
abbrev TestStore := List (String × Elf)

namespace TestStore

/-- Look up an entry by path. -/
def getElf? (store : TestStore) (path : String) : Option Elf :=
  (store.find? (·.fst == path)).map (·.snd)

/-- Mirror `Effects.io`'s `resolveDep`: enumerate candidate paths,
    take the first one in the store, compute canonical name. -/
def resolveDep (store : TestStore) (soname : String) (ctx : SearchContext) :
    Option (String × Runtime.FileHandle × Elf) :=
  (searchCandidates soname ctx).findSome? fun path =>
    (store.getElf? path).map fun elf =>
      (canonicalName path elf, (0 : Runtime.FileHandle), elf)

end TestStore

/-- The test `Effects` instance: `resolveDep` over the store, `fail`
    via `Except.error`. Closure captures the store. -/
def Effects.test (store : TestStore) : Effects (Except String) :=
  { resolveDep := fun soname ctx => .ok (store.resolveDep soname ctx)
    fail       := fun {_} msg    => .error msg }

-- ============================================================================
-- discoverPure — the test-side counterpart to `discover`. Takes the
-- in-memory store, the main object's path, and (optionally) an envPath,
-- and runs the BFS to completion in `Except String`.
-- ============================================================================

/-- Run the BFS to completion against a `TestStore`. The main object
    is looked up directly by path (no soname search for it — same as
    production `discover`). -/
def discoverPure (store : TestStore) (mainPath : String)
    (envPath : Option String := none) : Except String LoadGraph := do
  let some mainElf := store.getElf? mainPath
    | .error s!"discoverPure: main {mainPath} not in store"
  let mainName := canonicalName mainPath mainElf
  let mainObj : LoadedObject :=
    { name := mainName, handle := 0, elf := mainElf }
  discoverLoopWith (Effects.test store) envPath 64 (BfsState.initial mainObj)

-- ============================================================================
-- Behavior tests via `#guard`. Each scenario builds a small store, runs
-- discoverPure, and asserts properties of the resulting LoadGraph.
-- ============================================================================

-- All test paths start with `/` so soname-as-path resolution short-
-- circuits searchCandidates to a single literal lookup. Cleaner than
-- threading SearchContexts everywhere.

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

-- BFS order: main, b, c, d (b and c queued together; d via b first).
#guard match diamondGraph with
  | .ok g => (g.objects.map (·.name)) = #["main", "b", "c", "d"]
  | _     => false

-- Both `/b` (idx 1) and `/c` (idx 2) record an edge to `/d` (idx 3).
-- The second arrival (`/c → /d`) goes through the post-canonicalisation
-- dedup-hit branch in `bfsStep1.resolve`.
#guard match diamondGraph with
  | .ok g => g.deps = #[#[1, 2], #[3], #[3], #[]]
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

-- ---- 4. Canonical-name dedup -------------------------------------------
-- /main requests `/libfoo.so` and `/libfoo.so.1`. The file at
-- `/libfoo.so` has `DT_SONAME = "libfoo.so.1"`, so the second NEEDED
-- entry (which resolves to the actual file `/libfoo.so.1`) collides on
-- canonical name and the post-canonicalisation dedup-hit branch fires.

private def canonicalStore : TestStore := [
  ("/main",        mockElf (soname := some "main")
                            (needed := #["/libfoo.so", "/libfoo.so.1"])),
  ("/libfoo.so",   mockElf (soname := some "libfoo.so.1")),
  ("/libfoo.so.1", mockElf (soname := some "libfoo.so.1"))]

private def canonicalGraph : Except String LoadGraph := discoverPure canonicalStore "/main"

-- Two objects loaded (main + one libfoo); the second NEEDED dedups.
#guard match canonicalGraph with
  | .ok g => g.objects.size = 2
  | _     => false

-- Names: "main", "libfoo.so.1" (the canonical SONAME, not the path).
#guard match canonicalGraph with
  | .ok g => (g.objects.map (·.name)) = #["main", "libfoo.so.1"]
  | _     => false

-- main has TWO edges to libfoo (one per NEEDED entry), both to idx 1.
#guard match canonicalGraph with
  | .ok g => g.deps = #[#[1, 1], #[]]
  | _     => false

-- ---- 5. Missing dep -----------------------------------------------------
-- main NEEDs /missing which isn't in the store → resolveDep returns
-- none → bfsStep1 fires `eff.fail` → `.error` propagates out.

private def missingStore : TestStore := [
  ("/main", mockElf (soname := some "main") (needed := #["/missing"]))]

#guard (discoverPure missingStore "/main").isOk = false

-- ---- 6. Search-order precedence -----------------------------------------
-- env > runpath > defaults. The same bare soname `libx.so` exists in
-- both `/env/libx.so` and `/run/libx.so`; with envPath=`/env`, env wins.

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

end LeanLoad.Discover

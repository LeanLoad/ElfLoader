/-
Discover examples — pure, in-memory `#guard` scenarios.

The DFS traversal/finalization path is generic over the effect monad.
This file substitutes an in-memory `ExampleStore` for the filesystem, builds an
`ObjectFinder (Except String)` instance over it (using the same Discover search
policy as production), and exercises shape-level behaviors via `#guard` at
elaboration time:

  · Linear chain (4 objects in DFS pre-order).
  · Diamond (shared dep loaded once, two in-edges, DFS pre-order).
  · Cycle (A → B → A is loaded; DFS post-order deterministically breaks the
    cyclic init-order tie that gabi 08 leaves undefined).
  · Missing dep (returns `Except.error`).
  · Search-order precedence (env > runpath).

These are example-level checks. The integration path (real ELFs on disk
via `Runtime.File`) is exercised by `./run.sh` over
`examples/build/main`.

Canonical name = `elf.soname` (required) for NEEDED deps; `basename
mainPath` for the main entry. Matches the production object finder /
`discover` exactly. `mockElf` defaults `soname := some "anon"` so the
SONAME-required production policy is satisfied by default — examples
that want to exercise the SONAME-missing error path pass
`soname := none` explicitly.
-/

import LeanLoad.Discover.Finalize
import LeanLoad.Discover.Search

namespace LeanLoad.Discover

open LeanLoad
open LeanLoad.Parse (Elf)

private def dummyFile : Runtime.File :=
  { backing := .virtual
    size := 0
    read := fun range =>
      throw s!"discoverExample dummy file cannot read {range.size.toNat} bytes \
        at file offset 0x{range.off.toNat}" }

-- ============================================================================
--- Minimal Elf builder — only the fields Discover reads (`soname`, `runpath`,
-- `needed`) are interesting. Everything else gets a trivial value; the
-- segment / init / fini invariants discharge by `decide` on empty arrays.
-- ============================================================================

private def mockFileSize : ByteSize := 0

private def mockSegments : Parse.SegmentTable mockFileSize :=
  Parse.SegmentTable.empty

/-- Build a minimal `Elf` for Discover examples. `soname`, `runpath`,
    and `needed` are the only fields Discover observes; everything else is
    zeroed and the structural invariants discharge automatically.
    `soname` defaults to `some "anon"` because the production object finder
    *requires* DT_SONAME on every NEEDED dependency `.so`. Examples that want
    to exercise the SONAME-missing error path can pass `soname := none`
    explicitly. -/
private def mockElf (soname : Option String := some "anon")
    (rpath : Option String := none) (runpath : Option String := none)
    (needed : Array String := #[]) : Elf := {
  fileSize := mockFileSize
  machine  := .x86_64
  segments := mockSegments
  phdrTable := { off := 0, count := 0, map := .empty rfl }
  symtab   := #[]
  needed
  soname
  rpath
  runpath
  relocs := { rela := #[], jmprel := #[] }
  callTargets := Parse.CallTargets.empty mockSegments }

-- ============================================================================
-- ExampleStore — in-memory `path → Elf` map. It reuses the same pure
-- `Search.candidates` policy as production; only exact-path open is replaced by
-- a list lookup.
-- ============================================================================

/-- A `path → Elf` map for examples. Simple `List` for legibility — examples
    are 3-5 entries each. -/
private abbrev ExampleStore := List (String × Elf)

namespace ExampleStore

/-- Look up an entry by path. -/
private def getElf? (store : ExampleStore) (path : String) : Option Elf :=
  (store.find? (·.fst == path)).map (·.snd)

end ExampleStore

/-- Pure lexical directory used only by examples. Production uses
    `Search.canonicalOriginDir`, whose C shim provides the gABI-required
    canonical directory for `$ORIGIN`. -/
private def lexicalOriginDir (path : String) : Option String :=
  match path.splitOn "/" with
  | [] => none
  | [_] => some "."
  | parts =>
      let dirs := parts.dropLast
      let dir := String.intercalate "/" dirs
      if dir.isEmpty then some "/" else some dir

private def fileAtPath (_path : String) : Runtime.File :=
  dummyFile

/-- The example `ObjectFinder` instance: simulate production file lookup over an
    `ExampleStore`, with the same SONAME-required policy — `findSome?` skips entries whose elf has no DT_SONAME
    (treats them as "not found"; production throws). Closure captures
    both the store and a simulated `LD_LIBRARY_PATH`. -/
private def exampleFinder (store : ExampleStore) (envPath : Option String := none) :
    ObjectFinder (Except String) :=
  { findMain := fun mainPath =>
      match store.getElf? mainPath with
      | some mainElf =>
          .ok (DiscoveredObject.ofMain mainPath (fileAtPath mainPath)
            (lexicalOriginDir mainPath) mainElf)
      | none => .error s!"discoverExample: main {mainPath} not in store"
    findDependency := fun work => do
      let ctx : Search.Context :=
        { originDir := work.originDir, rpath := work.rpath, runpath := work.runpath, envPath }
      let paths ← Search.candidates work.needed ctx
      .ok <| paths.findSome? fun path =>
        (store.getElf? path).bind fun elf =>
          elf.soname.map fun name =>
            { name, handle := fileAtPath path, originDir := lexicalOriginDir path, elf } }

-- ============================================================================
-- discoverExample — the example-side counterpart to `discover`. Takes the
-- in-memory store, the main object's path, and (optionally) a simulated
-- envPath, and runs the DFS to completion in `Except String`.
-- ============================================================================

/-- Run the fully monadic Discover entry against an `ExampleStore`. The main
    object is looked up directly by path (no soname search for it — same as
    production main lookup). Main's canonical name is `basename
    mainPath` (via `DiscoveredObject.ofMain`, same as production). -/
private def discoverExample (store : ExampleStore) (mainPath : String)
    (envPath : Option String := none) : Except String Result := do
  discover (exampleFinder store envPath) 64 mainPath

-- ============================================================================
-- Behavior examples via `#guard`. Each scenario builds a small store, runs
-- discoverExample, and asserts properties of the resulting Discover result.
-- ============================================================================

-- Example paths starting with `/` short-circuit search to a literal
-- lookup, keeping the shape examples independent of search-context details.

-- ---- 1. Linear chain ----------------------------------------------------
-- /main → /b → /c → /d. Each elf needs the next one only.

private def linearStore : ExampleStore := [
  ("/main", mockElf (soname := some "main") (needed := #["/b"])),
  ("/b",    mockElf (soname := some "b")    (needed := #["/c"])),
  ("/c",    mockElf (soname := some "c")    (needed := #["/d"])),
  ("/d",    mockElf (soname := some "d"))]

private def linearResult : Except String Result := discoverExample linearStore "/main"

#guard match linearResult with
  | .ok r => r.graph.objects.size = 4
  | _     => false

#guard match linearResult with
  | .ok r => (r.graph.objects.map (·.name)) = #["main", "b", "c", "d"]
  | _     => false

-- main → b → c → d: each row depends only on the next.
#guard match linearResult with
  | .ok r => r.graph.deps = #[#[1], #[2], #[3], #[]]
  | _     => false

-- ---- 2. Diamond ---------------------------------------------------------
-- /main → {/b, /c}; /b → /d; /c → /d. Shared dep `/d` should load once.

private def diamondStore : ExampleStore := [
  ("/main", mockElf (soname := some "main") (needed := #["/b", "/c"])),
  ("/b",    mockElf (soname := some "b")    (needed := #["/d"])),
  ("/c",    mockElf (soname := some "c")    (needed := #["/d"])),
  ("/d",    mockElf (soname := some "d"))]

private def diamondResult : Except String Result := discoverExample diamondStore "/main"

-- `/d` appears once, four objects total.
#guard match diamondResult with
  | .ok r => r.graph.objects.size = 4
  | _     => false

-- DFS pre-order: main (0), then descend into /b — push b (1), descend
-- into /d — push d (2), back up to /c — push c (3). `/c → /d` resolves
-- as a dedup hit against d at idx 2.
#guard match diamondResult with
  | .ok r => (r.graph.objects.map (·.name)) = #["main", "b", "d", "c"]
  | _     => false

-- main (0) → {b (1), c (3)}; b (1) → d (2); d (2) → ∅; c (3) → d (2).
-- The shared dep `/d` is loaded once at idx 2; both b and c record
-- an edge to it (c's edge via the dedup-hit branch in `discoverWork`).
#guard match diamondResult with
  | .ok r => r.graph.deps = #[#[1, 3], #[2], #[], #[2]]
  | _     => false

-- DFS post-order init sequence: d before b/c, b/c before main.
#guard match diamondResult with
  | .ok r => r.initOrder.order.map (fun ix => ix.val) = #[2, 1, 3, 0]
  | _     => false

-- ---- 3. Cycle -----------------------------------------------------------
-- /main → /b → /main. The active-stack dedup check detects the back edge,
-- records it, and DFS post-order deterministically chooses b before main.

private def cycleStore : ExampleStore := [
  ("/main", mockElf (soname := some "main") (needed := #["/b"])),
  ("/b",    mockElf (soname := some "b")    (needed := #["/main"]))]

private def cycleResult : Except String Result := discoverExample cycleStore "/main"

#guard match cycleResult with
  | .ok r => (r.graph.objects.map (·.name)) = #["main", "b"]
  | _     => false

#guard match cycleResult with
  | .ok r => r.graph.deps = #[#[1], #[0]]
  | _     => false

#guard match cycleResult with
  | .ok r => r.initOrder.order.map (fun ix => ix.val) = #[1, 0]
  | _     => false

-- ---- 4. SONAME-based dedup ---------------------------------------------
-- main NEEDs both `/libfoo.so` and `/libfoo.so.1` — two different files
-- in the store, but BOTH have `DT_SONAME = "libfoo.so.1"`. Production
-- policy: dedup by SONAME. The second resolution hits the post-load
-- dedup branch via `findDiscoveredIdx`.

private def sonameStore : ExampleStore := [
  ("/main",        mockElf (soname := some "main")
                            (needed := #["/libfoo.so", "/libfoo.so.1"])),
  ("/libfoo.so",   mockElf (soname := some "libfoo.so.1")),
  ("/libfoo.so.1", mockElf (soname := some "libfoo.so.1"))]

private def sonameResult : Except String Result := discoverExample sonameStore "/main"

-- Two objects loaded (main + one libfoo); the second NEEDED dedups by SONAME.
#guard match sonameResult with
  | .ok r => r.graph.objects.size = 2
  | _     => false

#guard match sonameResult with
  | .ok r => (r.graph.objects.map (·.name)) = #["main", "libfoo.so.1"]
  | _     => false

-- main has two edges to libfoo (one per NEEDED entry), both to idx 1.
#guard match sonameResult with
  | .ok r => r.graph.deps = #[#[1, 1], #[]]
  | _     => false

-- ---- 5. Missing dep -----------------------------------------------------
-- main NEEDs /missing which isn't in the store → `ObjectFinder.findDependency`
-- returns none → traversal throws → `.error` propagates out.

private def missingStore : ExampleStore := [
  ("/main", mockElf (soname := some "main") (needed := #["/missing"]))]

#guard (discoverExample missingStore "/main").isOk = false

-- ---- 6. Search-order precedence -----------------------------------------
-- env > runpath. The same bare soname `libx.so` exists in both
-- `/env/libx.so` and `/run/libx.so`; with envPath=`/env`, env wins.

private def searchStore : ExampleStore := [
  ("/main",         mockElf (soname := some "main") (runpath := some "/run")
                             (needed := #["libx.so"])),
  ("/env/libx.so",  mockElf (soname := some "libx-from-env")),
  ("/run/libx.so",  mockElf (soname := some "libx-from-run"))]

#guard match discoverExample searchStore "/main" (envPath := some "/env") with
  | .ok r => (r.graph.objects.map (·.name)) = #["main", "libx-from-env"]
  | _     => false

-- Without envPath, runpath wins.
#guard match discoverExample searchStore "/main" (envPath := none) with
  | .ok r => (r.graph.objects.map (·.name)) = #["main", "libx-from-run"]
  | _     => false

-- ---- 7. SONAME-required for NEEDED deps --------------------------------
-- A NEEDED dep without DT_SONAME is rejected: the production object finder
-- throws; `exampleFinder` (matching policy) makes the entry invisible to
-- the store lookup (findSome? skips SONAME-less elves), surfacing as
-- the same "cannot find" diagnostic.

private def sonameMissingStore : ExampleStore := [
  ("/main",          mockElf (soname := some "main") (needed := #["/anonlib"])),
  ("/anonlib",       mockElf (soname := none))]    -- SONAME-less .so

#guard (discoverExample sonameMissingStore "/main").isOk = false

-- Main without SONAME is fine — main's canonical name is basename
-- mainPath, never elf.soname. Loads cleanly with no deps.
private def mainNoSonameStore : ExampleStore := [
  ("/main", mockElf (soname := none))]

#guard match discoverExample mainNoSonameStore "/main" with
  | .ok r => r.graph.objects.size = 1 ∧ r.graph.main.name = "main"
  | _     => false

end LeanLoad.Discover

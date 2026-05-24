/-
Discover examples — pure, in-memory `#guard` scenarios.

The DFS traversal/finalization path is generic over the effect monad.
This file substitutes an in-memory
`ExampleStore` for the filesystem, builds an `ObjectFinder (Except String)`
instance over it (re-simulating the C-side path search at the Lean
level), and exercises shape-level behaviors via `#guard` at
elaboration time:

  · Linear chain (4 objects in DFS pre-order).
  · Diamond (shared dep loaded once, two in-edges, DFS pre-order).
  · Cycle (A → B → A is rejected — gabi 08 leaves cyclic init order undefined).
  · Missing dep (returns `Except.error`).
  · Search-order precedence (env > runpath).

These are example-level checks. The integration path (real ELFs on disk
via `Runtime.FileOps.io`) is exercised by `./run.sh` over
`examples/build/main`.

Canonical name = `elf.soname` (required) for NEEDED deps; `basename
mainPath` for the main entry. Matches the production object finder /
`discover` exactly. `mockElf` defaults `soname := some "anon"` so the
SONAME-required production policy is satisfied by default — examples
that want to exercise the SONAME-missing error path pass
`soname := none` explicitly.
-/

import LeanLoad.Discover.Finalize

namespace LeanLoad.Discover

open LeanLoad
open LeanLoad.Parse (Elf)

-- ============================================================================
--- Minimal Elf builder — only the fields Discover reads (`soname`, `runpath`,
-- `needed`) are interesting. Everything else gets a trivial value; the
-- segment / init / fini invariants discharge by `decide` on empty arrays.
-- ============================================================================

/-- Build a minimal `Elf` for Discover examples. `soname`, `runpath`,
    and `needed` are the only fields Discover observes; everything else is
    zeroed and the structural invariants discharge automatically.
    `soname` defaults to `some "anon"` because the production object finder
    *requires* DT_SONAME on every NEEDED-loaded `.so`. Examples that want
    to exercise the SONAME-missing error path can pass `soname := none`
    explicitly. -/
private def mockHeader : Parse.ElfHeader :=
  { ident :=
      { magic := .elf
        ei_class := .class64
        ei_data := .lsb
        ei_version := .current
        ei_osabi := .none
        ei_abiversion := default
        pad0 := 0, pad1 := 0, pad2 := 0, pad3 := 0, pad4 := 0, pad5 := 0, pad6 := 0 }
    e_type := .dyn
    e_machine := .x86_64
    e_version := .current
    e_entry := 0
    e_phoff := 0
    e_shoff := 0
    e_flags := 0
    e_ehsize := 64
    e_phentsize := 56
    e_phnum := 0
    e_shentsize := 0
    e_shnum := 0
    e_shstrndx := .undef
    class64 := rfl
    littleEndian := rfl
    ehsizeOk := by decide
    phentsizeOk := by decide
    notExec := by decide }

private def mockElf (soname : Option String := some "anon")
    (runpath : Option String := none)
    (needed : Array String := #[]) : Elf := {
  header   := mockHeader
  symtab   := #[]
  needed
  soname
  runpath
  segments := Parse.SegmentTable.empty
  relocs := { rela := #[], jmprel := #[] }
  callTargets := Parse.CallTargets.empty Parse.SegmentTable.empty }

-- ============================================================================
-- ExampleStore — in-memory `path → Elf` map. Mirrors what the production
-- C runtime's `leanload_open_by_name` searches, but in Lean. The
-- `searchCandidates` simulator below is example-only — production path
-- resolution happens entirely in C.
-- ============================================================================

/-- A `path → Elf` map for examples. Simple `List` for legibility — examples
    are 3-5 entries each. -/
private abbrev ExampleStore := List (String × Elf)

namespace ExampleStore

/-- Look up an entry by path. -/
private def getElf? (store : ExampleStore) (path : String) : Option Elf :=
  (store.find? (·.fst == path)).map (·.snd)

end ExampleStore

/-- Mirror the C runtime's path search at the Lean level. Example-only —
    production goes through `Runtime.FileOps.io`. -/
private def exampleSearchCandidates (soname : String)
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

/-- The example `ObjectFinder` instance: simulate production file lookup over an
    `ExampleStore`, with the same SONAME-required policy — `findSome?` skips entries whose elf has no DT_SONAME
    (treats them as "not found"; production throws). Closure captures
    both the store and a simulated `LD_LIBRARY_PATH`. -/
private def exampleFinder (store : ExampleStore) (envPath : Option String := none) :
    ObjectFinder (Except String) :=
  { findMain := fun mainPath =>
      match store.getElf? mainPath with
      | some mainElf => .ok (LoadedObject.ofMain mainPath (default : Runtime.File) mainElf)
      | none => .error s!"discoverExample: main {mainPath} not in store"
    findDependency := fun work => .ok <|
      (exampleSearchCandidates work.needed work.runpath envPath).findSome? fun path =>
        (store.getElf? path).bind fun elf =>
          elf.soname.map fun name => { name, handle := (default : Runtime.File), elf } }

-- ============================================================================
-- discoverExample — the example-side counterpart to `discover`. Takes the
-- in-memory store, the main object's path, and (optionally) a simulated
-- envPath, and runs the DFS to completion in `Except String`.
-- ============================================================================

/-- Run the fully monadic Discover entry against an `ExampleStore`. The main
    object is looked up directly by path (no soname search for it — same as
    production main lookup). Main's canonical name is `basename
    mainPath` (via `LoadedObject.ofMain`, same as production). -/
private def discoverExample (store : ExampleStore) (mainPath : String)
    (envPath : Option String := none) : Except String LoadGraph := do
  discover (exampleFinder store envPath) 64 mainPath

-- ============================================================================
-- Behavior examples via `#guard`. Each scenario builds a small store, runs
-- discoverExample, and asserts properties of the resulting LoadGraph.
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

private def linearGraph : Except String LoadGraph := discoverExample linearStore "/main"

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

private def diamondStore : ExampleStore := [
  ("/main", mockElf (soname := some "main") (needed := #["/b", "/c"])),
  ("/b",    mockElf (soname := some "b")    (needed := #["/d"])),
  ("/c",    mockElf (soname := some "c")    (needed := #["/d"])),
  ("/d",    mockElf (soname := some "d"))]

private def diamondGraph : Except String LoadGraph := discoverExample diamondStore "/main"

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
-- an edge to it (c's edge via the dedup-hit branch in `discoverWork`).
#guard match diamondGraph with
  | .ok g => g.deps = #[#[1, 3], #[2], #[], #[2]]
  | _     => false

-- DFS post-order init sequence: d before b/c, b/c before main.
#guard match diamondGraph with
  | .ok g => g.initOrder.map (fun ix => ix.val) = #[2, 1, 3, 0]
  | _     => false

-- ---- 3. Cycle -----------------------------------------------------------
-- /main → /b → /main. The active-stack dedup check detects the back edge and
-- rejects the graph because cyclic init order is undefined by gabi 08.

private def cycleStore : ExampleStore := [
  ("/main", mockElf (soname := some "main") (needed := #["/b"])),
  ("/b",    mockElf (soname := some "b")    (needed := #["/main"]))]

private def cycleGraph : Except String LoadGraph := discoverExample cycleStore "/main"

#guard cycleGraph.isOk = false

-- ---- 4. SONAME-based dedup ---------------------------------------------
-- main NEEDs both `/libfoo.so` and `/libfoo.so.1` — two different files
-- in the store, but BOTH have `DT_SONAME = "libfoo.so.1"`. Production
-- policy: dedup by SONAME. The second resolution hits the post-load
-- dedup branch via `findLoadedIdx`.

private def sonameStore : ExampleStore := [
  ("/main",        mockElf (soname := some "main")
                            (needed := #["/libfoo.so", "/libfoo.so.1"])),
  ("/libfoo.so",   mockElf (soname := some "libfoo.so.1")),
  ("/libfoo.so.1", mockElf (soname := some "libfoo.so.1"))]

private def sonameGraph : Except String LoadGraph := discoverExample sonameStore "/main"

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
  | .ok g => (g.objects.map (·.name)) = #["main", "libx-from-env"]
  | _     => false

-- Without envPath, runpath wins.
#guard match discoverExample searchStore "/main" (envPath := none) with
  | .ok g => (g.objects.map (·.name)) = #["main", "libx-from-run"]
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
  | .ok g => g.objects.size = 1 ∧ g.main.name = "main"
  | _     => false

end LeanLoad.Discover

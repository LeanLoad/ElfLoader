/-
`LeanLoad.Discover` — assemble the dependency graph of an ELF.

Walks `DT_NEEDED` transitively: read main, parse, walk its needed
list, find each on disk via the search-path rules below, parse it,
walk its needed list, and so on. Output is a `DepGraph` of every
loaded object plus the object-index edges between them.

This is the IO stage of "where do files live"; `LeanLoad.Resolve` (pure)
takes over for "how do their bytes interact".

Search-path rules per gabi 08 § Shared Object Dependencies:
  1. If the name contains `/`, treat as a path directly.
  2. Else search in order: `LD_LIBRARY_PATH`, owning object's
     `DT_RUNPATH`, caller-supplied defaults.
  `DT_RPATH` is deprecated and intentionally not honoured.
-/

import LeanLoad.Parse.File
import LeanLoad.Runtime
import LeanLoad.Search

namespace LeanLoad.Discover

open LeanLoad
open LeanLoad.Parse
open LeanLoad.Search

/-- One loaded object. Identified by its `DT_SONAME` if present (else
    by the `DT_NEEDED` string we resolved through), and by the file
    path we read it from. -/
structure LoadedObject where
  /-- Canonical name (`DT_SONAME` if defined; otherwise the path
      basename or the resolving `DT_NEEDED` string). Used for
      deduplication. -/
  name : String
  /-- Filesystem path the bytes came from. -/
  path : String
  /-- Open read-only file handle, kept for `pread` (parsing extras)
      and `mmap` (Stage C). `none` for synthetic objects built by
      `LeanLoad.Fixtures` that have no backing file. -/
  handle : Option Runtime.FileHandle := none
  /-- Parsed ELF. -/
  elf  : File.ParsedElf

/-- Output of `Discover` — the dependency graph of the loaded image.
    The first entry of `objects` is `main`; remaining entries follow
    in BFS discovery order. `deps[i]` lists the indices of
    `objects[i]`'s `DT_NEEDED` entries (resolved at discover time);
    parallel-indexed with `objects` (`deps.size = objects.size`). -/
structure DepGraph where
  objects : Array LoadedObject
  deps    : Array (Array Nat)

namespace DepGraph

def main? (g : DepGraph) : Option LoadedObject :=
  g.objects[0]?

end DepGraph

/-- Open the file (read-only handle) and parse it via per-section
    `pread`s. The handle stays open for the loader's lifetime —
    used downstream by Map for file-backed `mmap`. -/
def readAndParse (path : String) : IO (Runtime.FileHandle × File.ParsedElf) := do
  let handle ← Runtime.open path
  let elf    ← File.parse handle
  pure (handle, elf)

/-- Find the first existing path among `paths`. -/
def firstExisting (paths : Array String) : IO (Option String) := do
  for p in paths do
    if (← System.FilePath.pathExists p) then return some p
  return none

/-- Resolve a `DT_NEEDED` string against the search context, returning
    the path on disk if found. -/
def resolveSoname (soname : String) (ctx : SearchContext) : IO (Option String) :=
  firstExisting (searchCandidates soname ctx)

/-- The canonical name we use to deduplicate a parsed ELF. Prefer
    `DT_SONAME`; fall back to the original `DT_NEEDED` string. -/
def canonicalName (needed : String) (elf : File.ParsedElf) : String :=
  elf.soname.getD needed

/-- The dedup primitive: is some object already loaded under this name?
    Pure; the BFS loop calls it before resolving / parsing each
    `DT_NEEDED` entry, and a second time after canonicalisation.
    Soundness lemma: `dedup_iff` in `Thm.Resolve`. -/
def alreadyLoaded (objs : Array LoadedObject) (name : String) : Bool :=
  objs.any (·.name == name)

/-- Resolve each object's `DT_NEEDED` strings to indices in `objects`.
    The BFS already stored objects under their canonical names; we
    just look each soname up. Pure post-pass over the BFS output. -/
def buildDeps (objects : Array LoadedObject) : Array (Array Nat) :=
  objects.map fun obj =>
    obj.elf.needed.filterMap fun soname =>
      objects.findIdx? (·.name == soname)

/-- BFS loop body. Recurses on `fuel`; each call processes at most
    one work item. Fuel = upper bound on total iterations; the BFS
    naturally terminates (`alreadyLoaded` rejects each name twice
    after first load), but Lean can't see that without an explicit
    bound, so we cap it. -/
private def discoverLoop (envPath : Option String) (fuel : Nat)
    (objs : Array LoadedObject) (work : List (Option String × String)) :
    IO (Array LoadedObject) := do
  match fuel with
  | 0 => return objs   -- bound exhausted; caller's responsibility to size it
  | fuel + 1 =>
    match work with
    | []            => return objs
    | (rp, sn) :: rest =>
      if alreadyLoaded objs sn then
        discoverLoop envPath fuel objs rest
      else
        let ctx : SearchContext := { runpath := rp, envPath, defaults := #[] }
        match ← resolveSoname sn ctx with
        | none =>
          throw (IO.userError s!"discover: cannot find '{sn}' (runpath={rp}, env={envPath})")
        | some path =>
          let (depHandle, dep) ← readAndParse path
          let canonical := canonicalName sn dep
          if alreadyLoaded objs canonical then
            discoverLoop envPath fuel objs rest
          else
            let objs' := objs.push { name := canonical, path, handle := some depHandle, elf := dep }
            -- BFS: append new pairs at the back so deeper deps come after siblings.
            let newPairs := dep.needed.toList.map fun n => (dep.runpath, n)
            discoverLoop envPath fuel objs' (rest ++ newPairs)

/-- Walk `DT_NEEDED` from `mainPath` transitively. Returns a
    `DepGraph` containing main and all reachable dependencies in
    BFS order. -/
def discover (mainPath : String) : IO DepGraph := do
  let (mainHandle, main) ← readAndParse mainPath
  let envPath ← IO.getEnv "LD_LIBRARY_PATH"
  let mainName := main.soname.getD mainPath
  let initObjs : Array LoadedObject :=
    #[{ name := mainName, path := mainPath, handle := some mainHandle, elf := main }]
  let initWork : List (Option String × String) :=
    main.needed.toList.map (fun n => (main.runpath, n))
  -- Fuel: a generous cap. Real binaries land in the low tens; 4096
  -- leaves headroom and still discharges termination at type-check.
  let objects ← discoverLoop envPath 4096 initObjs initWork
  return { objects, deps := buildDeps objects }

-- ============================================================================
-- Tests.
-- ============================================================================

/-- The full dependency graph of `build/main` should contain exactly
    five objects: main, libfoo.so, libbar.so, libbaz.so, libc.so.
    libbar↔libbaz form a cycle (mutual NEEDED); the SONAME-keyed
    dedup must terminate the BFS. -/
private def expectedNames : Array String :=
  #["main", "libfoo.so", "libbar.so", "libbaz.so", "libc.so"]

def test (g : DepGraph) : IO Nat := do
  let mut failures := 0
  let names := g.objects.map (·.name)

  if g.objects.size != expectedNames.size then
    IO.eprintln s!"expected {expectedNames.size} objects, got {g.objects.size}: {names}"
    failures := failures + 1

  for expected in expectedNames[1:] do
    if !names.any (· == expected) then
      IO.eprintln s!"{expected} missing from dependency graph: {names}"
      failures := failures + 1

  for nm in names do
    let occurrences := names.filter (· == nm) |>.size
    if occurrences > 1 then
      IO.eprintln s!"{nm} appears {occurrences} times — dedup failed"
      failures := failures + 1

  return failures

end LeanLoad.Discover

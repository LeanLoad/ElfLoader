/-
`LeanLoad.Discover` — assemble the dependency link map of an ELF.

Walks `DT_NEEDED` transitively: read main, parse, walk its needed
list, find each on disk via the search-path rules below, parse it,
walk its needed list, and so on. Output is a `LinkMap` mapping each
loaded object to its parsed form.

This is the IO stage of "where do files live"; `Spec.Resolve` (pure)
takes over for "how do their bytes interact".

Search-path rules per gabi 08 § Shared Object Dependencies:
  1. If the name contains `/`, treat as a path directly.
  2. Else search in order: `LD_LIBRARY_PATH`, owning object's
     `DT_RUNPATH`, caller-supplied defaults.
  `DT_RPATH` is deprecated and intentionally not honoured.
-/

import LeanLoad.Parse.File

namespace LeanLoad.Discover

open LeanLoad
open LeanLoad.Parse

-- ============================================================================
-- Search-path resolution (pure)
-- ============================================================================

/-- Split a colon-separated path list. Empty entries are dropped. -/
def parsePathList (s : String) : Array String :=
  s.splitOn ":" |>.filter (! ·.isEmpty) |>.toArray

#guard parsePathList "" = #[]
#guard parsePathList "/a:/b" = #["/a", "/b"]
#guard parsePathList "/a::/b" = #["/a", "/b"]

/-- Search context for one resolution call. -/
structure SearchContext where
  /-- The owning object's `DT_RUNPATH`, if any. Per-binary, not transitive. -/
  runpath  : Option String := none
  /-- Host's `LD_LIBRARY_PATH`, if set. -/
  envPath  : Option String := none
  /-- Caller-supplied default paths (`/lib`, `/usr/lib`, ...). Empty for
      hermetic tests. -/
  defaults : Array String  := #[]

/-- Enumerate candidate paths for `soname` under `ctx`. If `soname`
    contains `/` the result is `#[soname]` (treated as a path). -/
def searchCandidates (soname : String) (ctx : SearchContext) : Array String :=
  if soname.contains '/' then
    #[soname]
  else
    let dirs : Array String := Id.run do
      let mut acc : Array String := #[]
      if let some p := ctx.envPath  then acc := acc ++ parsePathList p
      if let some p := ctx.runpath  then acc := acc ++ parsePathList p
      acc := acc ++ ctx.defaults
      return acc
    dirs.map (fun d => s!"{d}/{soname}")

#guard searchCandidates "/abs/path" {} = #["/abs/path"]
#guard searchCandidates "libfoo.so" { runpath := some "/a:/b" } = #["/a/libfoo.so", "/b/libfoo.so"]

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
  /-- Parsed ELF. -/
  elf  : File.ParsedElf

/-- Output of `Discover`. The first entry is `main`; remaining entries
    follow in BFS discovery order. -/
structure LinkMap where
  objects : Array LoadedObject

namespace LinkMap

def main? (lm : LinkMap) : Option LoadedObject :=
  lm.objects[0]?

def find? (lm : LinkMap) (name : String) : Option LoadedObject :=
  lm.objects.find? (·.name == name)

def names (lm : LinkMap) : Array String :=
  lm.objects.map (·.name)

end LinkMap

/-- Read and parse an ELF file. -/
def readAndParse (path : String) : IO File.ParsedElf := do
  let bytes ← IO.FS.readBinFile path
  match File.parse bytes with
  | .ok e    => pure e
  | .error e => throw (IO.userError s!"parse {path}: {e}")

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

/-- Walk `DT_NEEDED` from `mainPath` transitively. Returns a
    `LinkMap` containing main and all reachable dependencies in
    BFS order. -/
partial def discover (mainPath : String) : IO LinkMap := do
  let main ← readAndParse mainPath
  let envPath ← IO.getEnv "LD_LIBRARY_PATH"
  let mainName := main.soname.getD mainPath
  let mut objs : Array LoadedObject :=
    #[{ name := mainName, path := mainPath, elf := main }]
  -- Worklist: pairs of (parent's runpath, soname to resolve).
  let mut work : List (Option String × String) :=
    main.needed.toList.map (fun n => (main.runpath, n))
  while !work.isEmpty do
    let (parentRunpath, soname) := work.head!
    work := work.tail!
    -- Already loaded?
    if objs.any (·.name == soname) then
      continue
    let ctx : SearchContext :=
      { runpath := parentRunpath, envPath, defaults := #[] }
    match (← resolveSoname soname ctx) with
    | none =>
      throw (IO.userError s!"discover: cannot find '{soname}' (runpath={parentRunpath}, env={envPath})")
    | some path =>
      let dep ← readAndParse path
      let canonical := canonicalName soname dep
      -- Re-check dedup against canonical name.
      if objs.any (·.name == canonical) then
        continue
      objs := objs.push { name := canonical, path, elf := dep }
      -- BFS: append at the back so deeper deps are processed after siblings.
      let newPairs := dep.needed.toList.map fun n => (dep.runpath, n)
      work := work ++ newPairs
  return { objects := objs }

end LeanLoad.Discover

-- ============================================================================
-- Tests.
-- ============================================================================
namespace LeanLoad.Discover.Test

/-- The full link map of `build/main` should be exactly five
    objects: main, libfoo.so, libbar.so, libbaz.so, libc.so.
    libbar↔libbaz form a cycle (mutual NEEDED); the SONAME-keyed
    dedup must terminate the BFS. -/
def expectedNames : Array String :=
  #["main", "libfoo.so", "libbar.so", "libbaz.so", "libc.so"]

def run (lm : LeanLoad.Discover.LinkMap) : IO Nat := do
  let mut failures := 0
  let names := lm.objects.map (·.name)

  if lm.objects.size != expectedNames.size then
    IO.eprintln s!"expected {expectedNames.size} objects, got {lm.objects.size}: {names}"
    failures := failures + 1

  for expected in expectedNames[1:] do
    if !names.any (· == expected) then
      IO.eprintln s!"{expected} missing from link map: {names}"
      failures := failures + 1

  for nm in names do
    let occurrences := names.filter (· == nm) |>.size
    if occurrences > 1 then
      IO.eprintln s!"{nm} appears {occurrences} times — dedup failed"
      failures := failures + 1

  return failures

end LeanLoad.Discover.Test

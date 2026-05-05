/-
`LeanLoad.Discover` — assemble the dependency closure of an ELF.

Walks `DT_NEEDED` transitively: read main, parse, walk its needed
list, find each on disk via `Link.Search.candidates`, parse it, walk
its needed list, and so on. Output is a `Closure` mapping each
loaded object to its parsed form.

This is the IO half of "linking"; `Link.Resolve` (pure) consumes the
result to perform symbol resolution.
-/

import LeanLoad.Parse
import LeanLoad.Link.Search

namespace LeanLoad.Discover

open LeanLoad
open LeanLoad.Parse

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
structure Closure where
  objects : Array LoadedObject

namespace Closure

def main? (li : Closure) : Option LoadedObject :=
  li.objects[0]?

def find? (li : Closure) (name : String) : Option LoadedObject :=
  li.objects.find? (·.name == name)

def names (li : Closure) : Array String :=
  li.objects.map (·.name)

end Closure

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
def resolveSoname (soname : String) (ctx : Link.Search.Context) : IO (Option String) :=
  firstExisting (Link.Search.candidates soname ctx)

/-- The canonical name we use to deduplicate a parsed ELF. Prefer
    `DT_SONAME`; fall back to the original `DT_NEEDED` string. -/
def canonicalName (needed : String) (elf : File.ParsedElf) : String :=
  elf.soname.getD needed

/-- Walk `DT_NEEDED` from `mainPath` transitively. Returns a
    `Closure` containing main and all reachable dependencies in
    BFS order. -/
partial def discover (mainPath : String) : IO Closure := do
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
    let ctx : Link.Search.Context :=
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

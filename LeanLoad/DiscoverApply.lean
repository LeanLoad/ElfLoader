/-
Discover executor — trusted IO.

The BFS file-walking loop, plus the IO leaves it calls
(`resolveSoname`, `readAndParse`). Decision-making and state
integration live in `DiscoverPlan`; this file just orchestrates IO
calls in the order the planner says.

Search-path rules per gabi 08 § Shared Object Dependencies:
  1. If the name contains `/`, treat as a path directly.
  2. Else search in order: `LD_LIBRARY_PATH`, owning object's
     `DT_RUNPATH`, caller-supplied defaults.
  `DT_RPATH` is deprecated and intentionally not honoured.
-/

import LeanLoad.DiscoverPlan
import LeanLoad.Parse.File
import LeanLoad.Runtime


namespace LeanLoad.Discover

open LeanLoad
open LeanLoad.Parse


-- ============================================================================
-- IO leaves
-- ============================================================================

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

-- ============================================================================
-- BFS executor
-- ============================================================================

/-- BFS loop: dispatches each `step` decision from `DiscoverPlan` to
    the right IO action, then `integrate`s the result. Recurses on
    `fuel`; the planner's natural termination (visited dedup) is
    invisible to Lean, so we cap with a generous bound. -/
private def discoverLoop (envPath : Option String) (fuel : Nat)
    (objs : Array LoadedObject) (work : List WorkItem) :
    IO (Array LoadedObject) := do
  match fuel with
  | 0 => return objs   -- bound exhausted; caller's responsibility to size it
  | fuel + 1 =>
    match step objs work with
    | .done => return objs
    | .skip rest => discoverLoop envPath fuel objs rest
    | .resolve sn rp rest =>
      let ctx : SearchContext := { runpath := rp, envPath, defaults := #[] }
      match ← resolveSoname sn ctx with
      | none =>
        throw (IO.userError s!"discover: cannot find '{sn}' (runpath={rp}, env={envPath})")
      | some path =>
        let (handle, parsedElf) ← readAndParse path
        let (objs', work') := integrate objs rest sn path handle parsedElf
        discoverLoop envPath fuel objs' work'

/-- Walk `DT_NEEDED` from `mainPath` transitively. Returns a
    `DepGraph` containing main and all reachable dependencies in
    BFS order. -/
def discover (mainPath : String) : IO DepGraph := do
  let (mainHandle, main) ← readAndParse mainPath
  let envPath ← IO.getEnv "LD_LIBRARY_PATH"
  let mainName := main.soname.getD mainPath
  let initObjs : Array LoadedObject :=
    #[{ name := mainName, path := mainPath, handle := some mainHandle, elf := main }]
  let initWork : List WorkItem :=
    main.needed.toList.map (fun n => (main.runpath, n))
  -- Fuel: a generous cap. Real binaries land in the low tens; 4096
  -- leaves headroom and still discharges termination at type-check.
  let objects ← discoverLoop envPath 4096 initObjs initWork
  return { objects, deps := buildDeps objects }

end LeanLoad.Discover

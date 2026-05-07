/-
Discover executor — trusted IO.

The BFS file-walking loop, plus the IO leaves it calls
(`resolveSoname`, `readAndParse`). Decision-making and state
integration live in `Plan.Discover`; this file just orchestrates IO
calls in the order the planner says.

Search-path rules per gabi 08 § Shared Object Dependencies:
  1. If the name contains `/`, treat as a path directly.
  2. Else search in order: `LD_LIBRARY_PATH`, owning object's
     `DT_RUNPATH`, caller-supplied defaults.
  `DT_RPATH` is deprecated and intentionally not honoured.
-/

import LeanLoad.Plan.Discover
import LeanLoad.Parse.RawElf
import LeanLoad.Elaborate.Elf
import LeanLoad.Runtime


namespace LeanLoad.Discover

open LeanLoad


-- ============================================================================
-- IO leaves
-- ============================================================================

/-- Open the file (read-only handle), byte-decode it, then elaborate
    PT_LOAD well-formedness AND group dynamic relocations by their
    target segment. The handle stays open for the loader's lifetime —
    used downstream by Exec for file-backed `mmap`.

    `Parse.parse` (I/O) and `Elaborate.elaborate` (pure) are separate
    stages so I/O failure (short read, missing section) is
    distinguishable from validation failure (well-formed bytes that
    violate gabi-07 / linker conventions, or relocations that fall
    outside any PT_LOAD). All I/O routes through the `rt` capability
    so tests can drive the loader against an in-memory filesystem. -/
def readAndParse (rt : Runtime.Ops) (path : String) :
    IO (Runtime.FileHandle × Elaborate.Elf) := do
  let handle ← rt.open path
  let raw    ← Parse.RawElf.parse rt handle
  let elf    ← IO.ofExcept (Elaborate.elaborate raw)
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

/-- BFS loop: dispatches each `step` decision from `Plan.Discover` to
    the right IO action, then `integrate`s the result. Recurses on
    `fuel`; the planner's natural termination (visited dedup) is
    invisible to Lean, so we cap with a generous bound.

    Threads the `0 < objs.size` invariant: every branch either keeps
    `objs` unchanged or appends via `integrate` (which only pushes or
    no-ops), preserving the bound. -/
private def discoverLoop (rt : Runtime.Ops) (envPath : Option String) (fuel : Nat)
    (objs : Array LoadedObject) (h : 0 < objs.size) (work : List WorkItem) :
    IO ObjectList := do
  match fuel with
  | 0 => pure (Subtype.mk objs h)
  | fuel + 1 =>
    match step objs work with
    | .done => pure (Subtype.mk objs h)
    | .skip rest => discoverLoop rt envPath fuel objs h rest
    | .resolve sn rp rest =>
      let ctx : SearchContext := { runpath := rp, envPath, defaults := #[] }
      match ← resolveSoname sn ctx with
      | none =>
        throw (IO.userError s!"discover: cannot find '{sn}' (runpath={rp}, env={envPath})")
      | some path =>
        let (handle, elf) ← readAndParse rt path
        let result := integrate objs rest sn path handle elf
        have h' : 0 < result.fst.size := integrate_size_pos objs rest sn path handle elf h
        discoverLoop rt envPath fuel result.fst h' result.snd

/-- Walk `DT_NEEDED` from `mainPath` transitively. Returns an
    `ObjectList` containing main and all reachable dependencies in
    BFS order — non-emptiness witnessed at the type level. -/
def discover (rt : Runtime.Ops) (mainPath : String) : IO ObjectList := do
  let (mainHandle, mainElf) ← readAndParse rt mainPath
  let envPath ← IO.getEnv "LD_LIBRARY_PATH"
  let mainName := canonicalName mainPath mainElf
  let initObjs : Array LoadedObject :=
    #[{ name := mainName, path := mainPath, handle := some mainHandle, elf := mainElf }]
  have h : 0 < initObjs.size := Nat.zero_lt_one
  let initWork : List WorkItem :=
    mainElf.needed.toList.map (fun n => (mainElf.runpath, n))
  -- Fuel: a generous cap. Real binaries land in the low tens; 4096
  -- leaves headroom and still discharges termination at type-check.
  discoverLoop rt envPath 4096 initObjs h initWork

end LeanLoad.Discover

/-
Discover executor — IO instantiation.

The BFS state machine (`bfsStep1`, `discoverLoopWith`) and its
invariant carrier (`BfsState`) live in `Discover.Step` — pure and
generic over the effect monad. This file:

  · Defines the two IO leaves — `resolveSoname` (filesystem search)
    and `readAndParse` (open + parse + elaborate).
  · Bundles them with `IO.userError`-shaped `fail` into `Effects.io`.
  · Provides `discover` — the production entry point. Constructs the
    initial `BfsState` from `mainPath`, then iterates the generic
    driver.

Tests can substitute `Effects.test` (over an in-memory store) for
`Effects.io` and call the same `discoverLoopWith` — no IO needed.

Search-path rules per gabi 08 § Shared Object Dependencies:
  1. If the name contains `/`, treat as a path directly.
  2. Else search in order: `LD_LIBRARY_PATH`, owning object's
     `DT_RUNPATH`, caller-supplied defaults.
  `DT_RPATH` is deprecated and intentionally not honoured.
-/

import LeanLoad.Discover.Step
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
    outside any PT_LOAD). -/
def readAndParse (path : String) :
    IO (Runtime.FileHandle × Elaborate.Elf) := do
  let handle ← Runtime.openFile path
  let raw    ← Parse.RawElf.parse handle
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
-- Effects instance for production IO.
-- ============================================================================

/-- The production IO instance: filesystem-backed `resolveSoname` /
    `readAndParse`, `IO.userError`-shaped `fail`. Tests substitute
    `Effects.test` (in-memory store) for this. -/
def Effects.io : Effects IO :=
  { resolveSoname := Discover.resolveSoname,
    readAndParse  := Discover.readAndParse,
    fail          := fun {_} msg => throw (IO.userError msg) }

-- ============================================================================
-- discover — production entry point.
-- ============================================================================

/-- Walk `DT_NEEDED` from `mainPath` transitively. Returns an
    `LoadGraph` containing main and all reachable dependencies in
    BFS order — non-emptiness, name-`Nodup`, and `deps`-coherence
    witnessed at the type level.

    Implemented as `BfsState.initial` followed by `discoverLoopWith`
    over the IO `Effects` instance. Fuel cap (4096) is invisible in
    practice — real binaries land in the low tens of objects. -/
def discover (mainPath : String) : IO LoadGraph := do
  let (mainHandle, mainElf) ← readAndParse mainPath
  let envPath ← IO.getEnv "LD_LIBRARY_PATH"
  let mainName := canonicalName mainPath mainElf
  let mainObj : LoadedObject := { name := mainName, handle := mainHandle, elf := mainElf }
  discoverLoopWith Effects.io envPath 4096 (BfsState.initial mainObj)

end LeanLoad.Discover

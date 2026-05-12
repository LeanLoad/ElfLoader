/-
Discover executor — trusted IO.

The BFS file-walking loop, plus the IO leaves it calls
(`resolveSoname`, `readAndParse`). Decision-making and state
integration live in `Discover.Plan`; this file just orchestrates IO
calls in the order the planner says.

Search-path rules per gabi 08 § Shared Object Dependencies:
  1. If the name contains `/`, treat as a path directly.
  2. Else search in order: `LD_LIBRARY_PATH`, owning object's
     `DT_RUNPATH`, caller-supplied defaults.
  `DT_RPATH` is deprecated and intentionally not honoured.
-/

import LeanLoad.Discover.Plan
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
-- BFS executor
-- ============================================================================

/-- BFS loop: dispatches each `step` decision from `Plan.Discover` to
    the right IO action, then integrates the result inline so both
    invariants (non-emptiness and name-`Nodup`) are derived at the
    push site. Recurses on `fuel`; the planner's natural termination
    (visited dedup) is invisible to Lean, so we cap with a generous
    bound. -/
private def discoverLoop (envPath : Option String) (fuel : Nat)
    (objs : Array LoadedObject)
    (h_pos : 0 < objs.size)
    (h_nodup : (objs.map (·.name)).toList.Nodup)
    (work : List WorkItem) :
    IO ObjectList := do
  match fuel with
  | 0 => pure ⟨objs, h_pos, h_nodup⟩
  | fuel + 1 =>
    match step objs work with
    | .done => pure ⟨objs, h_pos, h_nodup⟩
    | .skip rest => discoverLoop envPath fuel objs h_pos h_nodup rest
    | .resolve sn rp rest =>
      let ctx : SearchContext := { runpath := rp, envPath, defaults := #[] }
      match ← resolveSoname sn ctx with
      | none =>
        throw (IO.userError s!"discover: cannot find '{sn}' (runpath={rp}, env={envPath})")
      | some path =>
        let (handle, elf) ← readAndParse path
        let canonical := canonicalName path elf
        let obj : LoadedObject := { name := canonical, handle, elf }
        match h_fresh : alreadyLoaded objs canonical with
        | true =>
          -- Post-canonicalisation dedup hit. `obj` is dropped; both
          -- proofs carry forward unchanged.
          discoverLoop envPath fuel objs h_pos h_nodup rest
        | false =>
          -- Append and derive both invariants from the dedup miss.
          let objs' := objs.push obj
          have h_pos' : 0 < objs'.size := by
            show 0 < (objs.push obj).size
            rw [Array.size_push]; omega
          have h_nodup' : (objs'.map (·.name)).toList.Nodup :=
            nodup_names_push_of_alreadyLoaded_false objs obj h_nodup h_fresh
          discoverLoop envPath fuel objs' h_pos' h_nodup' (rest ++ workOfElf elf)

/-- Walk `DT_NEEDED` from `mainPath` transitively. Returns an
    `ObjectList` containing main and all reachable dependencies in
    BFS order — non-emptiness and name-`Nodup` witnessed at the type
    level. -/
def discover (mainPath : String) : IO ObjectList := do
  let (mainHandle, mainElf) ← readAndParse mainPath
  let envPath ← IO.getEnv "LD_LIBRARY_PATH"
  let mainName := canonicalName mainPath mainElf
  let initObjs : Array LoadedObject :=
    #[{ name := mainName, handle := mainHandle, elf := mainElf }]
  have h_pos : 0 < initObjs.size := Nat.zero_lt_one
  have h_nodup : (initObjs.map (·.name)).toList.Nodup := by
    simp [initObjs]
  -- Fuel: a generous cap. Real binaries land in the low tens; 4096
  -- leaves headroom and still discharges termination at type-check.
  discoverLoop envPath 4096 initObjs h_pos h_nodup (workOfElf mainElf)

end LeanLoad.Discover

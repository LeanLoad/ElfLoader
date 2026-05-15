/-
Discover executor — trusted IO.

The BFS file-walking loop, plus the IO leaves it calls
(`resolveSoname`, `readAndParse`). Decision-making, state integration,
and all `LoadGraph` invariant maintenance live in `Discover.Step`;
this file just orchestrates IO calls in the order the planner says.

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
-- BFS executor.
-- All `LoadGraph` invariant maintenance lives in `LoadGraph.recordDep`
-- and `LoadGraph.appendChild` (in `Discover.Step`). This loop just
-- threads the BFS state through `step`'s decisions and the IO leaves.
-- ============================================================================

/-- BFS loop: peel work items off `work`, dispatch each via `step` to
    either an immediate skip (already loaded) or an IO-bound resolve.
    Each branch updates the graph via the matching `LoadGraph` method.
    Recurses on `fuel`; the planner's natural termination (visited
    dedup) is invisible to Lean, so we cap with a generous bound. -/
private def discoverLoop (envPath : Option String) (fuel : Nat)
    (g : LoadGraph) (work : List WorkItem) : IO LoadGraph := do
  match fuel with
  | 0 => pure g
  | fuel + 1 =>
    match work with
    | [] => pure g
    | item :: rest =>
    match h_step : step g.objects item with
    | .skip tgt =>
      -- Already loaded. Record edge item.sourceIdx → tgt and continue.
      have h_tgt_lt : tgt < g.objects.size := step_skip_tgt_lt h_step
      discoverLoop envPath fuel (g.recordDep item.sourceIdx tgt h_tgt_lt) rest
    | .resolve =>
      let ctx : SearchContext := { runpath := item.runpath, envPath, defaults := #[] }
      match ← resolveSoname item.soname ctx with
      | none =>
        throw (IO.userError s!"discover: cannot find '{item.soname}' \
          (runpath={item.runpath}, env={envPath})")
      | some path =>
        let (handle, elf) ← readAndParse path
        let canonical := canonicalName path elf
        let obj : LoadedObject := { name := canonical, handle, elf }
        match h_idx : findLoadedIdx g.objects canonical with
        | some tgt =>
          -- Post-canonicalisation dedup hit. Drop `obj`, record the
          -- edge to the existing object's index.
          have h_tgt_lt : tgt < g.objects.size :=
            findLoadedIdx_lt g.objects canonical h_idx
          discoverLoop envPath fuel (g.recordDep item.sourceIdx tgt h_tgt_lt) rest
        | none =>
          -- Genuinely new object. `appendChild` pushes it, records the
          -- edge `item.sourceIdx → newIdx`, and maintains all four
          -- LoadGraph invariants (size, nodup, depsSize, depsBounds).
          have h_fresh : alreadyLoaded g.objects canonical = false := by
            -- findLoadedIdx = findIdx? — both expand to "no obj satisfies
            -- (·.name == canonical)". Convert via Array.findIdx?_eq_none_iff
            -- and Array.any_eq_false.
            have h_none : Array.findIdx? (·.name == canonical) g.objects = none :=
              h_idx
            have h_all_ne := Array.findIdx?_eq_none_iff.mp h_none
            unfold alreadyLoaded
            rw [Bool.eq_false_iff]
            intro h_any
            rw [Array.any_eq_true'] at h_any
            obtain ⟨o, h_mem, h_eq⟩ := h_any
            exact absurd (h_all_ne o h_mem) (by simp [h_eq])
          let newIdx := g.objects.size
          discoverLoop envPath fuel (g.appendChild item.sourceIdx obj h_fresh)
            (rest ++ workOfElf newIdx elf)

/-- Walk `DT_NEEDED` from `mainPath` transitively. Returns an
    `LoadGraph` containing main and all reachable dependencies in
    BFS order — non-emptiness, name-`Nodup`, and `deps`-coherence
    witnessed at the type level. -/
def discover (mainPath : String) : IO LoadGraph := do
  let (mainHandle, mainElf) ← readAndParse mainPath
  let envPath ← IO.getEnv "LD_LIBRARY_PATH"
  let mainName := canonicalName mainPath mainElf
  let initObjs : Array LoadedObject :=
    #[{ name := mainName, handle := mainHandle, elf := mainElf }]
  let initDeps : Array (Array Nat) := #[#[]]
  let g₀ : LoadGraph := {
    objects    := initObjs
    deps       := initDeps
    sizePos    := Nat.zero_lt_one
    namesNodup := by simp [initObjs]
    depsSize   := by simp [initDeps, initObjs]
    depsBounds := by
      intro i h_lt t h_mem
      have h_i_zero : i = 0 := by
        have h_lt' : i < (#[#[]] : Array (Array Nat)).size := h_lt
        simp at h_lt'; omega
      subst h_i_zero
      have h_get : initDeps[0]'h_lt = (#[] : Array Nat) := rfl
      rw [h_get] at h_mem
      exact absurd h_mem (by simp) }
  -- Fuel: a cap that's invisible in practice. Each iteration either
  -- drops a work item (`.skip` / `.done` / dedup-hit branch) or pushes
  -- one new object; both monotone toward termination. Real binaries
  -- land in the low tens of objects; 4096 is generous.
  discoverLoop envPath 4096 g₀ (workOfElf 0 mainElf)

end LeanLoad.Discover

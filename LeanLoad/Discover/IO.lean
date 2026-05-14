/-
Discover executor — trusted IO.

The BFS file-walking loop, plus the IO leaves it calls
(`resolveSoname`, `readAndParse`). Decision-making and state
integration live in `Discover.Step`; this file just orchestrates IO
calls in the order the planner says.

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
-- Edge accumulation. Pure helpers — kept private to this file since
-- `discover` is the only producer of `LoadGraph.deps`.
-- ============================================================================

/-- Add an out-edge `src → tgt` to `deps`. `Array.modify` returns the
    array unchanged when `src` is out of range, but in practice every
    `src` we pass came from a `WorkItem` we emitted, so the in-range
    case is the only one ever exercised. -/
private def recordEdge (deps : Array (Array Nat)) (src tgt : Nat) :
    Array (Array Nat) :=
  deps.modify src (·.push tgt)

private theorem recordEdge_size (deps : Array (Array Nat)) (src tgt : Nat) :
    (recordEdge deps src tgt).size = deps.size := by
  unfold recordEdge; exact Array.size_modify

/-- If every existing target was `< N` and the new target is `< N`,
    then every target after `recordEdge` is `< N`. -/
private theorem recordEdge_bounds (deps : Array (Array Nat)) (src tgt : Nat)
    {N : Nat}
    (h_bounds : ∀ (i : Nat) (h : i < deps.size), ∀ t ∈ deps[i], t < N)
    (h_tgt : tgt < N) :
    ∀ (i : Nat) (h : i < (recordEdge deps src tgt).size),
      ∀ t ∈ (recordEdge deps src tgt)[i], t < N := by
  intro i h_lt t h_mem
  have h_lt_orig : i < deps.size := by rw [recordEdge_size] at h_lt; exact h_lt
  -- Unfold the modify via Array.getElem_modify (returns `if`-form).
  have h_get :
      (recordEdge deps src tgt)[i]'h_lt =
        (if src = i then (·.push tgt) deps[i] else deps[i]) := by
    unfold recordEdge
    exact Array.getElem_modify h_lt
  rw [h_get] at h_mem
  by_cases h_eq : src = i
  · rw [if_pos h_eq] at h_mem
    rcases Array.mem_push.mp h_mem with h_old | h_eq_t
    · exact h_bounds i h_lt_orig t h_old
    · subst h_eq_t; exact h_tgt
  · rw [if_neg h_eq] at h_mem
    exact h_bounds i h_lt_orig t h_mem

/-- The `.skip` arm of `step` carries `tgt < objs.size`, because
    `step` produces `.skip` only when `findLoadedIdx` returned the
    matching index — which is bounded by `findLoadedIdx_lt`. -/
private theorem step_skip_tgt_lt {objs : Array LoadedObject}
    {work : List WorkItem} {src tgt : Nat} {rest : List WorkItem}
    (h : step objs work = .skip src tgt rest) :
    tgt < objs.size := by
  unfold step at h
  match work, h with
  | (_, _, sn) :: _, h =>
    simp only at h
    split at h
    · rename_i tgt' h_find
      have h_eq : tgt = tgt' := by
        injection h with _ h_tgt _
        exact h_tgt.symm
      rw [h_eq]
      exact findLoadedIdx_lt objs sn h_find
    · cases h

-- ============================================================================
-- BFS executor
-- ============================================================================

/-- BFS loop: dispatches each `step` decision from `Discover.Step` to
    the right IO action, then integrates the result inline so all four
    invariants (non-emptiness, name-`Nodup`, `deps.size = objs.size`,
    bounded edge targets) are derived at the push site. Recurses on
    `fuel`; the planner's natural termination (visited dedup) is
    invisible to Lean, so we cap with a generous bound. -/
private def discoverLoop (envPath : Option String) (fuel : Nat)
    (objs : Array LoadedObject)
    (deps : Array (Array Nat))
    (h_pos : 0 < objs.size)
    (h_nodup : (objs.map (·.name)).toList.Nodup)
    (h_deps_size : deps.size = objs.size)
    (h_deps_bounds : ∀ (i : Nat) (h : i < deps.size),
      ∀ t ∈ deps[i], t < objs.size)
    (work : List WorkItem) :
    IO LoadGraph := do
  match fuel with
  | 0 => pure ⟨objs, deps, h_pos, h_nodup, h_deps_size, h_deps_bounds⟩
  | fuel + 1 =>
    match h_step : step objs work with
    | .done => pure ⟨objs, deps, h_pos, h_nodup, h_deps_size, h_deps_bounds⟩
    | .skip src tgt rest =>
      -- Already loaded. Record edge src → tgt and continue.
      let deps' := recordEdge deps src tgt
      have h_tgt_lt : tgt < objs.size := step_skip_tgt_lt h_step
      have h_size' : deps'.size = objs.size := by
        rw [recordEdge_size]; exact h_deps_size
      have h_bounds' : ∀ (i : Nat) (h : i < deps'.size),
          ∀ t ∈ deps'[i], t < objs.size :=
        recordEdge_bounds deps src tgt h_deps_bounds h_tgt_lt
      discoverLoop envPath fuel objs deps' h_pos h_nodup h_size' h_bounds' rest
    | .resolve src sn rp rest =>
      let ctx : SearchContext := { runpath := rp, envPath, defaults := #[] }
      match ← resolveSoname sn ctx with
      | none =>
        throw (IO.userError s!"discover: cannot find '{sn}' (runpath={rp}, env={envPath})")
      | some path =>
        let (handle, elf) ← readAndParse path
        let canonical := canonicalName path elf
        let obj : LoadedObject := { name := canonical, handle, elf }
        match h_canonical_idx : findLoadedIdx objs canonical with
        | some tgt =>
          -- Post-canonicalisation dedup hit. Drop `obj`, record the
          -- edge `src → tgt` (the existing object's index).
          let deps' := recordEdge deps src tgt
          have h_size' : deps'.size = objs.size := by
            rw [recordEdge_size]; exact h_deps_size
          have h_tgt_lt : tgt < objs.size :=
            findLoadedIdx_lt objs canonical h_canonical_idx
          have h_bounds' : ∀ (i : Nat) (h : i < deps'.size),
              ∀ t ∈ deps'[i], t < objs.size :=
            recordEdge_bounds deps src tgt h_deps_bounds h_tgt_lt
          discoverLoop envPath fuel objs deps' h_pos h_nodup h_size' h_bounds' rest
        | none =>
          -- Genuinely new object. Append; record edge `src → newIdx`
          -- (where newIdx = objs.size, valid in the post-push array).
          -- The new object's row in `deps` starts empty; subsequent
          -- BFS steps fill it as its NEEDED items resolve.
          have h_fresh : alreadyLoaded objs canonical = false := by
            -- findLoadedIdx = findIdx? — both expand to "no obj satisfies
            -- (·.name == canonical)". Convert via Array.findIdx?_eq_none_iff
            -- and Array.any_eq_false.
            have h_none : Array.findIdx? (·.name == canonical) objs = none :=
              h_canonical_idx
            have h_all_ne :=
              Array.findIdx?_eq_none_iff.mp h_none
            unfold alreadyLoaded
            rw [Bool.eq_false_iff]
            intro h_any
            rw [Array.any_eq_true'] at h_any
            obtain ⟨o, h_mem, h_eq⟩ := h_any
            exact absurd (h_all_ne o h_mem) (by simp [h_eq])
          let newIdx := objs.size
          let objs' := objs.push obj
          let deps_with_edge := recordEdge deps src newIdx
          let deps' := deps_with_edge.push #[]
          have h_pos' : 0 < objs'.size := by
            show 0 < (objs.push obj).size
            rw [Array.size_push]; omega
          have h_nodup' : (objs'.map (·.name)).toList.Nodup :=
            nodup_names_push_of_alreadyLoaded_false objs obj h_nodup h_fresh
          have h_size_re : deps_with_edge.size = objs.size := by
            rw [recordEdge_size]; exact h_deps_size
          have h_size' : deps'.size = objs'.size := by
            show (deps_with_edge.push #[]).size = (objs.push obj).size
            rw [Array.size_push, Array.size_push, h_size_re]
          have h_old_bounds_lifted : ∀ (i : Nat) (h : i < deps.size),
              ∀ t ∈ deps[i], t < objs'.size := by
            intro i h_lt_i t h_mem
            have := h_deps_bounds i h_lt_i t h_mem
            show t < (objs.push obj).size
            rw [Array.size_push]; omega
          have h_newIdx_lt : newIdx < objs'.size := by
            show objs.size < (objs.push obj).size
            rw [Array.size_push]; omega
          have h_bounds_re : ∀ (i : Nat) (h : i < deps_with_edge.size),
              ∀ t ∈ deps_with_edge[i], t < objs'.size :=
            recordEdge_bounds deps src newIdx h_old_bounds_lifted h_newIdx_lt
          have h_bounds' : ∀ (i : Nat) (h : i < deps'.size),
              ∀ t ∈ deps'[i], t < objs'.size := by
            intro i h_lt t h_mem
            have h_split : i < deps_with_edge.size ∨ i = deps_with_edge.size := by
              have h_lt' : i < (deps_with_edge.push #[]).size := h_lt
              rw [Array.size_push] at h_lt'; omega
            rcases h_split with h_lt_old | h_eq
            · have h_get : deps'[i]'h_lt = deps_with_edge[i]'h_lt_old := by
                show (deps_with_edge.push #[])[i]'h_lt = _
                rw [Array.getElem_push, dif_pos h_lt_old]
              rw [h_get] at h_mem
              exact h_bounds_re i h_lt_old t h_mem
            · subst h_eq
              have h_get : deps'[deps_with_edge.size]'h_lt = (#[] : Array Nat) := by
                show (deps_with_edge.push #[])[deps_with_edge.size]'h_lt = _
                rw [Array.getElem_push, dif_neg (Nat.lt_irrefl _)]
              rw [h_get] at h_mem
              exact absurd h_mem (by simp)
          discoverLoop envPath fuel objs' deps' h_pos' h_nodup' h_size' h_bounds'
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
  have h_pos : 0 < initObjs.size := Nat.zero_lt_one
  have h_nodup : (initObjs.map (·.name)).toList.Nodup := by
    simp [initObjs]
  have h_deps_size : initDeps.size = initObjs.size := by
    simp [initDeps, initObjs]
  have h_deps_bounds : ∀ (i : Nat) (h : i < initDeps.size),
      ∀ t ∈ initDeps[i], t < initObjs.size := by
    intro i h_lt t h_mem
    have h_i_zero : i = 0 := by
      have h_lt' : i < (#[#[]] : Array (Array Nat)).size := h_lt
      simp at h_lt'; omega
    subst h_i_zero
    have h_get : initDeps[0]'h_lt = (#[] : Array Nat) := rfl
    rw [h_get] at h_mem
    exact absurd h_mem (by simp)
  -- Fuel: a cap that's invisible in practice. Each iteration either
  -- drops a work item (`.skip` / `.done` / dedup-hit branch) or pushes
  -- one new object; both monotone toward termination. Real binaries
  -- land in the low tens of objects; 4096 is generous.
  discoverLoop envPath 4096 initObjs initDeps h_pos h_nodup h_deps_size h_deps_bounds
    (workOfElf 0 mainElf)

end LeanLoad.Discover

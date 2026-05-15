/-
Discover planner — pure.

The graph-construction logic plus the search-path resolution rules,
separated from the IO loop. Given the current `(objs, work)` state,
decides what to do next; given a just-parsed dep, integrates it. No
file IO, no parsing — those live in `LeanLoad.Discover.IO`.

Mirrors the `Reloc.plan` / `Init.plan` / `Exec.realize` pattern:
pure decision + state update, IO bookend orchestrator.

Spec: gabi 08 § Shared Object Dependencies (BFS dedup + search rules).

Search rules:
  1. If the soname contains `/`, treat it as a path directly
     (no search performed).
  2. Otherwise search in order: `LD_LIBRARY_PATH`, owning object's
     `DT_RUNPATH`, caller-supplied defaults.
  `DT_RPATH` is deprecated and intentionally not honoured.

File layout (top-to-bottom dependency order):
  · Search-path resolution (parsePathList, SearchContext, searchCandidates)
  · LoadedObject (one entry of the graph)
  · Pure dedup primitives + soundness (canonicalName, alreadyLoaded,
    findLoadedIdx, nodup_names_push_of_alreadyLoaded_false)
  · Edge accumulation (recordEdge + size/bounds preservation)
  · LoadGraph (the BFS state = output bundle) + LoadGraph.{main,
    recordDep, appendChild} — the methods bundle invariant maintenance
    so `discoverLoop` only calls them.
  · WorkItem, StepResult, step (BFS state machine + per-item decision)
-/

import LeanLoad.Parse.RawElf
import LeanLoad.Elaborate.Elf
import LeanLoad.Runtime

namespace LeanLoad.Discover

open LeanLoad
open LeanLoad.Parse

-- ============================================================================
-- Search-path resolution (pure helpers, used by `Discover.resolveSoname`)
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

-- ============================================================================
-- LoadedObject — one entry of the graph.
-- ============================================================================

/-- One loaded object. Identified by its `DT_SONAME` if present (else
    by the `DT_NEEDED` string we resolved through). -/
structure LoadedObject where
  /-- Canonical name (`DT_SONAME` if defined; otherwise the path
      basename or the resolving `DT_NEEDED` string). Used for
      deduplication. -/
  name : String
  /-- Open read-only file handle, kept for `pread` (parsing extras)
      and `mmap` (Map stage). Synthetic objects built by
      `LeanLoad.Example` use a `FileHandle.mock` with empty bytes;
      production paths always carry a real fd. -/
  handle : Runtime.FileHandle
  /-- Elaborated ELF — output of `Elaborate.elaborate` after
      `Parse.parse`. The type itself is the witness that PT_LOAD
      well-formedness held and every dynamic relocation was located
      against a covering segment. -/
  elf  : Elaborate.Elf

-- ============================================================================
-- Pure dedup primitives.
--
-- The BFS uses `alreadyLoaded` (Bool dedup check) before pushing, and
-- `findLoadedIdx` (returns the matching index for edge recording).
-- `canonicalName` assigns the dedup key from a path + parsed elf.
-- ============================================================================

/-- The canonical name we use to deduplicate an elaborated ELF.
    Prefer `DT_SONAME`; fall back to the path's basename. The path
    fallback gives a *file-canonical* dedup key — two `DT_NEEDED`
    strings that resolve to the same file get the same key even
    when `DT_SONAME` is absent. Basename (rather than full path)
    keeps the name short for diagnostics; collisions only occur
    when loading two different files with the same filename, which
    is unusual. -/
def canonicalName (path : String) (elf : Elaborate.Elf) : String :=
  elf.soname.getD ((path.splitOn "/").getLast?.getD path)

/-- The dedup primitive: is some object already loaded under this name?
    Pure; the BFS loop calls it before resolving / parsing each
    `DT_NEEDED` entry, and a second time after canonicalisation. -/
def alreadyLoaded (objs : Array LoadedObject) (name : String) : Bool :=
  objs.any (·.name == name)

/-- Linear search for an object by name. Defined via `Array.findIdx?`
    so the size bound (`findLoadedIdx_lt` below) drops out of the core
    `Array.of_findIdx?_eq_some` characterisation. Used by the BFS to
    record dep edges to already-loaded objects. -/
def findLoadedIdx (objs : Array LoadedObject) (name : String) : Option Nat :=
  objs.findIdx? (·.name == name)

/-- The index returned by `findLoadedIdx` is `< objs.size`. -/
theorem findLoadedIdx_lt (objs : Array LoadedObject) (name : String) {idx : Nat}
    (h : findLoadedIdx objs name = some idx) : idx < objs.size := by
  have h_match := Array.of_findIdx?_eq_some (xs := objs) (p := (·.name == name)) h
  -- The match yields `objs[idx]? = some _` (else `false = true`).
  match h_get : objs[idx]? with
  | some _ =>
    obtain ⟨h_lt, _⟩ := Array.getElem?_eq_some_iff.mp h_get
    exact h_lt
  | none =>
    rw [h_get] at h_match
    exact absurd h_match (by simp)

/-- The BFS dedup primitive returns `true` iff some loaded object
    already carries the given name. -/
theorem alreadyLoaded_iff
    (objs : Array LoadedObject) (name : String) :
    alreadyLoaded objs name = true ↔ ∃ obj ∈ objs, obj.name = name := by
  unfold alreadyLoaded
  rw [Array.any_eq_true']
  simp

/-- Dedup primitive's correctness: if the loop's invariant
    `objs.names` is `Nodup` holds and the next candidate's name passes
    the `alreadyLoaded` check (returns `false`), pushing it preserves
    the invariant. Consumed by `LoadGraph.appendChild`. -/
theorem nodup_names_push_of_alreadyLoaded_false
    (objs : Array LoadedObject) (obj : LoadedObject)
    (h_nodup : (objs.map (·.name)).toList.Nodup)
    (h_fresh : alreadyLoaded objs obj.name = false) :
    ((objs.push obj).map (·.name)).toList.Nodup := by
  rw [Array.map_push, Array.toList_push, List.nodup_append]
  refine ⟨h_nodup, by simp, ?_⟩
  intro a ha b hb hab
  rw [List.mem_singleton] at hb
  subst hb
  have h_in : ∃ o ∈ objs, o.name = obj.name := by
    obtain ⟨o, ho_mem, ho_name⟩ := Array.mem_map.mp (Array.mem_toList_iff.mp ha)
    exact ⟨o, ho_mem, ho_name.trans hab⟩
  exact (Bool.eq_false_iff.mp h_fresh) ((alreadyLoaded_iff objs obj.name).mpr h_in)

-- ============================================================================
-- Edge accumulation. The push primitive over `deps`'s `Array (Array Nat)`
-- shape, plus its size + bounds preservation lemmas. Both LoadGraph
-- methods (`recordDep`, `appendChild`) consume these to maintain the
-- per-LoadGraph invariants in one place.
-- ============================================================================

/-- Add an out-edge `src → tgt` to `deps`. `Array.modify` returns the
    array unchanged when `src` is out of range, but in practice every
    `src` we pass came from a `WorkItem` we emitted, so the in-range
    case is the only one ever exercised. -/
def recordEdge (deps : Array (Array Nat)) (src tgt : Nat) :
    Array (Array Nat) :=
  deps.modify src (·.push tgt)

theorem recordEdge_size (deps : Array (Array Nat)) (src tgt : Nat) :
    (recordEdge deps src tgt).size = deps.size := by
  unfold recordEdge; exact Array.size_modify

/-- If every existing target was `< N` and the new target is `< N`,
    then every target after `recordEdge` is `< N`. -/
theorem recordEdge_bounds (deps : Array (Array Nat)) (src tgt : Nat)
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

-- ============================================================================
-- LoadGraph — the BFS state carrier and final discovery output.
-- ============================================================================

/-- Output of `Discover` — the loaded objects in BFS discovery order
    with `main` at index 0. Carries the structural invariants needed
    by every downstream consumer:

      * `sizePos` — `0 < val.size`. `discover` seeds with main and
        BFS only pushes, so non-emptiness holds by construction.
        Makes `main` total (no `Option`).

      * `namesNodup` — names are pairwise distinct. The BFS dedups
        via canonical SONAME before pushing.

      * `deps` — for each object index `i`, the indices of objects it
        depends on. Recorded directly during BFS (the source/target
        pair is known at edge-creation time), so it survives any
        mismatch between `DT_NEEDED` strings and canonical
        (`DT_SONAME` / basename) names. `Init.order` consumes this
        directly — no name-based re-derivation, no silent drops.

      * `depsSize` — `deps.size = objects.size`. Maintained by every push.

      * `depsBounds` — every recorded edge target is a valid index
        into `objects`. Maintained because edges only originate from
        `findLoadedIdx` (iterates `[:objs.size]`) or from the index
        about to be pushed (always `< objs.size + 1`).

    Access pattern: `g.objects[i]` (indexed) / `for obj in g.objects do`
    (iteration). Use `g.main` for the main executable instead of
    `g.objects[0]?`. -/
structure LoadGraph where
  /-- The loaded objects, in BFS discovery order. Main at index 0. -/
  objects    : Array LoadedObject
  /-- Per-object dependency indices, recorded during BFS. -/
  deps       : Array (Array Nat)
  /-- Non-emptiness — `0 < objects.size`. Witnessed by `discover`
      seeding with `main` before entering the BFS loop. -/
  sizePos    : 0 < objects.size
  /-- Names pairwise distinct. Witnessed by the BFS `alreadyLoaded`
      dedup check. -/
  namesNodup : (objects.map (·.name)).toList.Nodup
  /-- `deps` is parallel to `objects`. -/
  depsSize   : deps.size = objects.size
  /-- Every recorded edge target is a valid index into `objects`. -/
  depsBounds : ∀ (i : Nat) (h : i < deps.size), ∀ t ∈ deps[i], t < objects.size

namespace LoadGraph

/-- The main executable — total because `LoadGraph` carries the
    non-emptiness witness. -/
def main (g : LoadGraph) : LoadedObject := g.objects[0]'g.sizePos

/-- Record a dep edge `src → tgt` to an already-loaded object. The
    target's bound is the caller's obligation — `discoverLoop` discharges
    it from `step_skip_tgt_lt` (BFS dedup hit) or `findLoadedIdx_lt`
    (post-canonicalisation dedup hit). All four `LoadGraph` invariants
    are preserved by `recordEdge_size` + `recordEdge_bounds`; objects
    and namesNodup are untouched. -/
def recordDep (g : LoadGraph) (src tgt : Nat) (h_tgt : tgt < g.objects.size) :
    LoadGraph :=
  { g with
    deps       := recordEdge g.deps src tgt
    depsSize   := by rw [recordEdge_size]; exact g.depsSize
    depsBounds := recordEdge_bounds g.deps src tgt g.depsBounds h_tgt }

/-- Append a freshly-discovered object as `g.objects.size`'s entry,
    plus the dep edge `src → newIdx` from the requesting object. The
    fresh row in `deps` starts empty; subsequent BFS steps fill it as
    the new object's NEEDED items resolve. The `h_fresh` precondition
    (no existing object carries this name) is what
    `nodup_names_push_of_alreadyLoaded_false` needs to preserve
    `namesNodup`. -/
def appendChild (g : LoadGraph) (src : Nat) (obj : LoadedObject)
    (h_fresh : alreadyLoaded g.objects obj.name = false) :
    LoadGraph :=
  let newIdx       := g.objects.size
  let objs'        := g.objects.push obj
  let depsWithEdge := recordEdge g.deps src newIdx
  let deps'        := depsWithEdge.push #[]
  have h_pos' : 0 < objs'.size := by rw [Array.size_push]; omega
  have h_size_re : depsWithEdge.size = g.objects.size := by
    rw [recordEdge_size]; exact g.depsSize
  have h_size' : deps'.size = objs'.size := by
    show (depsWithEdge.push #[]).size = (g.objects.push obj).size
    rw [Array.size_push, Array.size_push, h_size_re]
  -- Lift the old-deps bound to the new (larger) objects array, then
  -- chain through `recordEdge_bounds` and the trailing `push #[]`.
  have h_old_bounds_lifted : ∀ (i : Nat) (h : i < g.deps.size),
      ∀ t ∈ g.deps[i], t < objs'.size := by
    intro i h_lt_i t h_mem
    have h_t := g.depsBounds i h_lt_i t h_mem
    show t < (g.objects.push obj).size
    rw [Array.size_push]; omega
  have h_newIdx_lt : newIdx < objs'.size := by
    show g.objects.size < (g.objects.push obj).size
    rw [Array.size_push]; omega
  have h_bounds_re : ∀ (i : Nat) (h : i < depsWithEdge.size),
      ∀ t ∈ depsWithEdge[i], t < objs'.size :=
    recordEdge_bounds g.deps src newIdx h_old_bounds_lifted h_newIdx_lt
  have h_bounds' : ∀ (i : Nat) (h : i < deps'.size),
      ∀ t ∈ deps'[i], t < objs'.size := by
    intro i h_lt t h_mem
    have h_split : i < depsWithEdge.size ∨ i = depsWithEdge.size := by
      have h_lt' : i < (depsWithEdge.push #[]).size := h_lt
      rw [Array.size_push] at h_lt'; omega
    rcases h_split with h_lt_old | h_eq
    · have h_get : deps'[i]'h_lt = depsWithEdge[i]'h_lt_old := by
        show (depsWithEdge.push #[])[i]'h_lt = _
        rw [Array.getElem_push, dif_pos h_lt_old]
      rw [h_get] at h_mem
      exact h_bounds_re i h_lt_old t h_mem
    · subst h_eq
      have h_get : deps'[depsWithEdge.size]'h_lt = (#[] : Array Nat) := by
        show (depsWithEdge.push #[])[depsWithEdge.size]'h_lt = _
        rw [Array.getElem_push, dif_neg (Nat.lt_irrefl _)]
      rw [h_get] at h_mem
      exact absurd h_mem (by simp)
  { objects    := objs'
    deps       := deps'
    sizePos    := h_pos'
    namesNodup :=
      nodup_names_push_of_alreadyLoaded_false g.objects obj g.namesNodup h_fresh
    depsSize   := h_size'
    depsBounds := h_bounds' }

end LoadGraph

-- ============================================================================
-- BFS state machine: WorkItem queue + per-item decision (`step`).
-- The queue is managed by `discoverLoop`; `step` is called only on a
-- concrete head element.
-- ============================================================================

/-- One BFS work item: a `DT_NEEDED` soname, with its source-object
    context. `sourceIdx` identifies the object whose `DT_NEEDED`
    produced this item — `discoverLoop` records the dep edge once the
    target is resolved. `runpath` carries the source's `DT_RUNPATH`
    for search-path resolution. -/
structure WorkItem where
  sourceIdx : Nat
  runpath   : Option String
  soname    : String

/-- The result of looking up `item.soname` in the loaded objects. -/
inductive StepResult where
  /-- Soname already loaded — record edge `item.sourceIdx → targetIdx`. -/
  | skip (targetIdx : Nat)
  /-- Soname is new — needs IO to resolve to a path, open, and parse. -/
  | resolve

/-- Pure step: dispatch on whether the work item's soname is already
    loaded. Returns the matching index for the `.skip` branch's edge
    recording. The `.done` case (empty work queue) is handled by the
    caller — `step` is only invoked on a concrete item. -/
def step (objs : Array LoadedObject) (item : WorkItem) : StepResult :=
  match findLoadedIdx objs item.soname with
  | some tgt => .skip tgt
  | none     => .resolve

/-- New work items spawned by a freshly elaborated elf at `sourceIdx`:
    one per `DT_NEEDED` entry, tagged with the providing object's
    runpath. -/
def workOfElf (sourceIdx : Nat) (elf : Elaborate.Elf) : List WorkItem :=
  elf.needed.toList.map fun n =>
    { sourceIdx, runpath := elf.runpath, soname := n }

/-- The `.skip` arm of `step` carries `tgt < objs.size`, because
    `step` produces `.skip` only when `findLoadedIdx` returned the
    matching index — which is bounded by `findLoadedIdx_lt`. -/
theorem step_skip_tgt_lt {objs : Array LoadedObject}
    {item : WorkItem} {tgt : Nat}
    (h : step objs item = .skip tgt) :
    tgt < objs.size := by
  unfold step at h
  split at h
  · rename_i tgt' h_find
    have h_eq : tgt = tgt' := by injection h with h_tgt; exact h_tgt.symm
    rw [h_eq]
    exact findLoadedIdx_lt objs item.soname h_find
  · cases h

end LeanLoad.Discover

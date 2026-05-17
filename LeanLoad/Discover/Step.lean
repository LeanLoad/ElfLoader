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
  · Pure dedup primitives + soundness (canonicalName, findLoadedIdx,
    findLoadedIdx_lt, findLoadedIdx_none_iff, nodup_names_push_…)
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
-- The BFS uses `findLoadedIdx` to both dedup and (in the `.skip` arm)
-- recover the matching index for edge recording. `canonicalName`
-- assigns the dedup key from a path + parsed elf.
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

/-- Linear search for an object by name. Defined via `Array.findIdx?`
    so the size bound (`findLoadedIdx_lt` below) drops out of the core
    `Array.of_findIdx?_eq_some` characterisation. The BFS calls this
    once per `DT_NEEDED` to dedup before resolving, and once more after
    canonicalisation to catch the SONAME-rename case. -/
def findLoadedIdx (objs : Array LoadedObject) (name : String) : Option Nat :=
  objs.findIdx? (·.name == name)

/-- The index returned by `findLoadedIdx` is `< objs.size`. -/
theorem findLoadedIdx_lt (objs : Array LoadedObject) (name : String) {idx : Nat}
    (h : findLoadedIdx objs name = some idx) : idx < objs.size := by
  have h_match := Array.of_findIdx?_eq_some (xs := objs) (p := (·.name == name)) h
  match h_get : objs[idx]? with
  | some _ =>
    obtain ⟨h_lt, _⟩ := Array.getElem?_eq_some_iff.mp h_get
    exact h_lt
  | none =>
    rw [h_get] at h_match
    exact absurd h_match (by simp)

/-- `findLoadedIdx = none` characterised: no object in `objs` carries
    the given name. -/
theorem findLoadedIdx_none_iff (objs : Array LoadedObject) (name : String) :
    findLoadedIdx objs name = none ↔ ∀ o ∈ objs, o.name ≠ name := by
  unfold findLoadedIdx
  rw [Array.findIdx?_eq_none_iff]
  simp

/-- Pushing a freshly-loaded object preserves the names-Nodup invariant.
    The precondition `findLoadedIdx = none` is what `bfsStep1` discharges
    by pattern-matching on its dedup check (no extra proof construction
    required at the call site). -/
theorem nodup_names_push_of_findLoadedIdx_none
    (objs : Array LoadedObject) (obj : LoadedObject)
    (h_nodup : (objs.map (·.name)).toList.Nodup)
    (h_fresh : findLoadedIdx objs obj.name = none) :
    ((objs.push obj).map (·.name)).toList.Nodup := by
  rw [Array.map_push, Array.toList_push, List.nodup_append]
  refine ⟨h_nodup, by simp, ?_⟩
  intro a ha b hb hab
  rw [List.mem_singleton] at hb
  subst hb
  obtain ⟨o, ho_mem, ho_name⟩ := Array.mem_map.mp (Array.mem_toList_iff.mp ha)
  have h_ne : o.name ≠ obj.name :=
    (findLoadedIdx_none_iff objs obj.name).mp h_fresh o ho_mem
  exact h_ne (ho_name.trans hab)

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
  /-- Names pairwise distinct. Witnessed by the BFS `findLoadedIdx`
      dedup check before each push. -/
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
    `nodup_names_push_of_findLoadedIdx_none` needs to preserve
    `namesNodup`. -/
def appendChild (g : LoadGraph) (src : Nat) (obj : LoadedObject)
    (h_fresh : findLoadedIdx g.objects obj.name = none) :
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
      nodup_names_push_of_findLoadedIdx_none g.objects obj g.namesNodup h_fresh
    depsSize   := h_size'
    depsBounds := h_bounds' }

/-- `recordDep` doesn't touch the `objects` array. -/
@[simp] theorem recordDep_objects (g : LoadGraph) (src tgt : Nat)
    (h_tgt : tgt < g.objects.size) :
    (g.recordDep src tgt h_tgt).objects = g.objects := rfl

/-- Corollary used wherever a size proof needs to survive `recordDep`. -/
@[simp] theorem recordDep_size (g : LoadGraph) (src tgt : Nat)
    (h_tgt : tgt < g.objects.size) :
    (g.recordDep src tgt h_tgt).objects.size = g.objects.size := rfl

/-- `appendChild` pushes one entry — the size grows by exactly one. -/
@[simp] theorem appendChild_size (g : LoadGraph) (src : Nat) (obj : LoadedObject)
    (h_fresh : findLoadedIdx g.objects obj.name = none) :
    (g.appendChild src obj h_fresh).objects.size = g.objects.size + 1 := by
  show (g.objects.push obj).size = _; rw [Array.size_push]

/-- The pushed object lives at the old size (= new size - 1). -/
@[simp] theorem appendChild_objects (g : LoadGraph) (src : Nat) (obj : LoadedObject)
    (h_fresh : findLoadedIdx g.objects obj.name = none) :
    (g.appendChild src obj h_fresh).objects = g.objects.push obj := rfl

/-- `main` is at index 0 in both old and new graphs, so it's preserved. -/
theorem appendChild_main (g : LoadGraph) (src : Nat) (obj : LoadedObject)
    (h_fresh : findLoadedIdx g.objects obj.name = none) :
    (g.appendChild src obj h_fresh).main = g.main := by
  show (g.objects.push obj)[0]'_ = g.objects[0]'_
  rw [Array.getElem_push, dif_pos g.sizePos]

/-- The pushed object is at the back of the new `objects` array. -/
theorem appendChild_back (g : LoadGraph) (src : Nat) (obj : LoadedObject)
    (h_fresh : findLoadedIdx g.objects obj.name = none) :
    (g.appendChild src obj h_fresh).objects.back? = some obj := by
  show (g.objects.push obj).back? = some obj
  simp [Array.back?]

/-- `recordDep` preserves `main`. -/
theorem recordDep_main (g : LoadGraph) (src tgt : Nat)
    (h_tgt : tgt < g.objects.size) :
    (g.recordDep src tgt h_tgt).main = g.main := rfl

end LoadGraph

-- ============================================================================
-- BFS state machine: WorkItem queue + per-item decision (`step`).
-- The queue is managed by `bfsStep1` / `discoverLoopWith`; `step` is
-- called only on a concrete head element.
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

/-- `step` returns `.skip tgt` iff `findLoadedIdx` returned `some tgt`.
    Each branch is a direct match — useful for tests that want to
    assert which dispatch branch fires on a given input. -/
theorem step_skip_iff {objs : Array LoadedObject} {item : WorkItem} {tgt : Nat} :
    step objs item = .skip tgt ↔ findLoadedIdx objs item.soname = some tgt := by
  constructor
  · intro h
    unfold step at h
    split at h
    · rename_i tgt' h_find
      injection h with h_tgt; rw [← h_tgt]; exact h_find
    · cases h
  · intro h
    unfold step
    rw [h]

/-- `step` returns `.resolve` iff `findLoadedIdx` returned `none`. -/
theorem step_resolve_iff {objs : Array LoadedObject} {item : WorkItem} :
    step objs item = .resolve ↔ findLoadedIdx objs item.soname = none := by
  constructor
  · intro h
    unfold step at h
    split at h
    · cases h
    · assumption
  · intro h
    unfold step
    rw [h]

/-- The `.skip` arm of `step` carries `tgt < objs.size`, because
    `step` produces `.skip` only when `findLoadedIdx` returned the
    matching index — which is bounded by `findLoadedIdx_lt`. -/
theorem step_skip_tgt_lt {objs : Array LoadedObject}
    {item : WorkItem} {tgt : Nat}
    (h : step objs item = .skip tgt) :
    tgt < objs.size :=
  findLoadedIdx_lt objs item.soname (step_skip_iff.mp h)

/-- `workOfElf` items all carry `sourceIdx = sourceIdx`. Used by
    `bfsStep1` to maintain the BFS-state invariant after pushing a new
    object's NEEDED entries onto the queue. -/
theorem workOfElf_sourceIdx (sourceIdx : Nat) (elf : Elaborate.Elf)
    {item : WorkItem} (h_mem : item ∈ workOfElf sourceIdx elf) :
    item.sourceIdx = sourceIdx := by
  unfold workOfElf at h_mem
  rw [List.mem_map] at h_mem
  obtain ⟨_, _, h_eq⟩ := h_mem
  rw [← h_eq]

-- ============================================================================
-- BfsState — the BFS carrier with one structural invariant: every
-- pending work item's `sourceIdx` is a valid object index. This is
-- maintained by `bfsStep1` across iterations and lets callers
-- (`Materialize`-shaped reasoning, tests) treat every queued source
-- as a `Fin graph.objects.size` without an `Option` dance.
-- ============================================================================

/-- BFS carrier: the accumulating `LoadGraph` plus the pending work
    queue, bundled with the invariant that every queued item's
    `sourceIdx` is in range for the current graph.

    Initial state: `initBfsState`. Per-iteration state evolution:
    `bfsStep1`. End state: `work = []` (no more sonames to resolve).
    All transitions preserve `workSourcesValid`, so it never has to
    be re-proven at consumer sites. -/
structure BfsState where
  graph            : LoadGraph
  work             : List WorkItem
  /-- Every queued item's source object exists. Maintained because:
      · `.skip` / `.resolve-dedup-hit` drop the head and don't grow
        objects — tail items remain valid by record-projection.
      · `.resolve-new` grows objects (so old bounds still hold by
        `<-of-<` monotonicity) and the new `workOfElf` items all carry
        `sourceIdx = newIdx < (g.appendChild …).objects.size`. -/
  workSourcesValid : ∀ item ∈ work, item.sourceIdx < graph.objects.size

namespace BfsState

/-- Initial BFS state: the main object alone, with its NEEDED entries
    queued. `workSourcesValid` holds because every initial work item
    has `sourceIdx = 0 < 1 = (initial graph).objects.size`. -/
def initial (mainObj : LoadedObject) : BfsState :=
  let graph : LoadGraph := {
    objects    := #[mainObj]
    deps       := #[#[]]
    sizePos    := Nat.zero_lt_one
    namesNodup := by simp
    depsSize   := rfl
    depsBounds := by
      intro i h_lt t h_mem
      have h_i_zero : i = 0 := by
        have h_lt' : i < (#[#[]] : Array (Array Nat)).size := h_lt
        simp at h_lt'; omega
      subst h_i_zero
      exact absurd h_mem (by simp) }
  let work := workOfElf 0 mainObj.elf
  { graph, work,
    workSourcesValid := by
      intro item h_mem
      rw [workOfElf_sourceIdx 0 mainObj.elf h_mem]
      show 0 < graph.objects.size
      exact graph.sizePos }

/-- The initial graph holds exactly `mainObj`. -/
@[simp] theorem initial_objects (mainObj : LoadedObject) :
    (initial mainObj).graph.objects = #[mainObj] := rfl

/-- The initial graph's `main` projection returns the seed. -/
@[simp] theorem initial_main (mainObj : LoadedObject) :
    (initial mainObj).graph.main = mainObj := rfl

/-- The initial work queue is exactly `mainObj.elf`'s `DT_NEEDED`
    entries (one `WorkItem` per entry, sourceIdx = 0). -/
@[simp] theorem initial_work (mainObj : LoadedObject) :
    (initial mainObj).work = workOfElf 0 mainObj.elf := rfl

end BfsState

-- ============================================================================
-- Effects — abstract IO leaves so `bfsStep1` is generic over the
-- effect monad. Production: `IO` via `Effects.io` (defined in
-- `Discover/IO.lean`). Tests: synthetic monad over an in-memory
-- store via `Effects.test`.
-- ============================================================================

/-- The single IO leaf `bfsStep1` calls, plus a `fail` for the
    missing-dep error. Parameterised over the effect monad `m` so
    tests can swap in a pure `Except String` (or `ReaderT TestStore`)
    instance. -/
structure Effects (m : Type → Type) where
  /-- Resolve a `DT_NEEDED` soname against the search context, open
      the file, parse it, and elaborate. Returns:
      · `none` — soname didn't resolve to an existing file (missing dep).
      · `some (name, handle, elf)` — `name` is the canonical dedup key
        (`DT_SONAME` if set, else the path basename), `handle` is the
        open fd (kept for downstream `mmap`), `elf` is the elaborated
        view.
      Parse/elaborate failures escape via the monad's error mechanism
      (IO exception in production; `throw` in `Except`-based tests).
      Splitting "not found" out as a `none` instead of using `fail`
      lets `bfsStep1` produce the diagnostic with full `WorkItem`
      context (runpath, envPath) that the effect doesn't know about. -/
  resolveDep : String → SearchContext →
               m (Option (String × Runtime.FileHandle × Elaborate.Elf))
  /-- Surface a fatal error. In `IO`, this is `throw (IO.userError …)`;
      in `Except String`, it's `throw`. Polymorphic in the return type
      because the caller is in continuation position. -/
  fail       : {α : Type} → String → m α

-- ============================================================================
-- bfsStep1 — one BFS iteration. Pure interface, generic over `m`,
-- consumes/produces `BfsState` so the invariant is type-enforced
-- across steps. The driver `discoverLoopWith` just iterates this.
-- ============================================================================

/-- Result of one BFS iteration: either the queue was empty (`done`,
    `s.graph` is the final output) or one item was processed
    (`continue s'`, with `s'.workSourcesValid` preserved). -/
inductive BfsStepResult where
  | done
  | continue (s' : BfsState)

/-- Process exactly one work item.

    Returns `.done` if the queue is empty (terminal state — caller
    should return `s.graph`). Otherwise dispatches the head via `step`
    and one of three branches:

    · `.skip` — soname already loaded. Edge recorded via
      `LoadGraph.recordDep`, queue tail unchanged.
    · `.resolve` + post-canonicalisation dedup hit — drop the
      re-parsed object, record edge to existing index.
    · `.resolve` + new object — push via `LoadGraph.appendChild`,
      enqueue the new elf's NEEDED entries via `workOfElf`.

    In each branch, `workSourcesValid` is re-established from the
    pre-existing invariant plus locally available bounds. -/
def bfsStep1 {m : Type → Type} [Monad m] (eff : Effects m)
    (envPath : Option String) (s : BfsState) : m BfsStepResult := do
  match h_work : s.work with
  | [] => pure .done
  | item :: rest =>
    -- The invariant gives us bounds on every queued item, including
    -- those still in `rest` (which we'll re-queue or drop).
    have h_rest_valid : ∀ i ∈ rest, i.sourceIdx < s.graph.objects.size := by
      intro i hi
      exact s.workSourcesValid i (by rw [h_work]; exact List.mem_cons_of_mem _ hi)
    match h_step : step s.graph.objects item with
    | .skip tgt =>
      have h_tgt : tgt < s.graph.objects.size := step_skip_tgt_lt h_step
      let g' := s.graph.recordDep item.sourceIdx tgt h_tgt
      -- recordDep_size: g'.objects.size = s.graph.objects.size (rfl), so
      -- tail bounds carry over verbatim.
      pure (.continue { graph := g', work := rest, workSourcesValid := h_rest_valid })
    | .resolve =>
      let ctx : SearchContext := { runpath := item.runpath, envPath, defaults := #[] }
      match ← eff.resolveDep item.soname ctx with
      | none =>
        eff.fail s!"discover: cannot find '{item.soname}' \
          (runpath={item.runpath}, env={envPath})"
      | some (canonical, handle, elf) =>
        let obj : LoadedObject := { name := canonical, handle, elf }
        match h_idx : findLoadedIdx s.graph.objects canonical with
        | some tgt =>
          -- Post-canonicalisation dedup hit. Edge to existing index.
          have h_tgt : tgt < s.graph.objects.size :=
            findLoadedIdx_lt _ _ h_idx
          let g' := s.graph.recordDep item.sourceIdx tgt h_tgt
          pure (.continue { graph := g', work := rest, workSourcesValid := h_rest_valid })
        | none =>
          -- New object. The dedup match arm gives us `h_idx :
          -- findLoadedIdx … = none` directly — `appendChild`'s
          -- precondition. No further proof construction needed.
          let newIdx := s.graph.objects.size
          let g' := s.graph.appendChild item.sourceIdx obj h_idx
          -- After appendChild, g'.objects.size = s.graph.objects.size + 1.
          -- Old rest items had sourceIdx < old size, still < new size.
          -- New workOfElf items have sourceIdx = newIdx = old size < new size.
          have h_g_size : g'.objects.size = s.graph.objects.size + 1 :=
            LoadGraph.appendChild_size _ _ _ _
          let newWork := workOfElf newIdx elf
          have h_all_valid : ∀ i ∈ rest ++ newWork,
              i.sourceIdx < g'.objects.size := by
            intro i hi
            rcases List.mem_append.mp hi with hL | hR
            · have h_old := h_rest_valid i hL
              rw [h_g_size]; omega
            · rw [workOfElf_sourceIdx newIdx elf hR, h_g_size]
              show s.graph.objects.size < s.graph.objects.size + 1
              omega
          pure (.continue { graph := g', work := rest ++ newWork,
                            workSourcesValid := h_all_valid })

-- ============================================================================
-- discoverLoopWith — iterate `bfsStep1` until the queue empties (or
-- fuel runs out). The fuel cap is invisible in practice; each push
-- monotonically grows `objects.size`, and `objects.size ≤ total
-- transitive deps in the system`.
-- ============================================================================

/-- Drive the BFS to completion using the given effects. Returns
    `s.graph` once the work queue empties. The fuel cap is a Lean-
    termination concession — the natural termination (queue shrinks
    to empty) is invisible to the type system. -/
def discoverLoopWith {m : Type → Type} [Monad m] (eff : Effects m)
    (envPath : Option String) (fuel : Nat) (s : BfsState) : m LoadGraph := do
  match fuel with
  | 0 => pure s.graph
  | fuel + 1 =>
    match ← bfsStep1 eff envPath s with
    | .done => pure s.graph
    | .continue s' => discoverLoopWith eff envPath fuel s'

end LeanLoad.Discover

/-
BFS driver — the algorithm, generic over the effect monad.

Three layers, top-down:

  · Per-item dispatch (`WorkItem` / `Decision` / `dispatch` / `workOfElf`).
    Pure: given the loaded objects and one queued item, decide whether
    to skip (already loaded) or resolve (defer to the IO seam).

  · State carrier (`BfsState`) — accumulating `LoadGraph` + pending
    work queue + one invariant (`workSourcesValid`: every queued
    item's `sourceIdx` is a valid object index).

  · State-update helpers (`linkExisting`, `appendAndQueue`) and the
    `step` / `discoverLoopWith` driver. Each branch's invariant
    maintenance sits in its helper so `step` reads as a flat dispatch
    table.

Effects are abstract — `Effects m` from `Discover/Effects.lean`.
Production wires `Effects.io` over `IO` in `Discover/IO.lean`; tests
wire `Effects.test` over `Except String` in `Discover/Test.lean`.
Same driver, two effects.
-/

import LeanLoad.Discover.Graph
import LeanLoad.Discover.Effects

namespace LeanLoad.Discover

open LeanLoad

-- ============================================================================
-- WorkItem + Decision + dispatch.
-- ============================================================================

/-- One BFS work item: a `DT_NEEDED` soname, with its source-object
    context. `sourceIdx` identifies the object whose `DT_NEEDED`
    produced this item — `BfsState.step` records the dep edge once the
    target is resolved. `runpath` carries the source's `DT_RUNPATH`
    for search-path resolution. -/
structure WorkItem where
  /-- The `DT_NEEDED` string to resolve. Identifying field — first so
      `#guard` output is most readable. -/
  soname    : String
  /-- Index of the object in `LoadGraph.objects` whose NEEDED list
      produced this item. `BfsState.step` records the dep edge once
      the target is resolved. -/
  sourceIdx : Nat
  /-- The source object's `DT_RUNPATH`, threaded through the search
      context for path resolution. -/
  runpath   : Option String

/-- The result of `dispatch`: looking up `item.soname` in the loaded
    objects either hits (skip) or misses (resolve via IO). -/
inductive Decision where
  /-- Soname already loaded — record edge `item.sourceIdx → targetIdx`. -/
  | skip (targetIdx : Nat)
  /-- Soname is new — needs IO to resolve to a path, open, and parse. -/
  | resolve

/-- Pure dispatch: decide whether the work item's soname is already
    loaded. Returns the matching index for the `.skip` branch's edge
    recording. The `.done` case (empty work queue) is handled by the
    caller — `dispatch` is only invoked on a concrete item.

    Note: this is the *pre-IO* dedup, keyed on the raw `DT_NEEDED`
    string. A second dedup happens inside `step` after IO returns,
    keyed on the canonical `DT_SONAME` (see `linkExisting`'s second
    call site). Pre-IO dedup is an optimization — it skips
    `resolveDep` when the same string was already resolved. -/
def dispatch (objs : Array LoadedObject) (item : WorkItem) : Decision :=
  match findLoadedIdx objs item.soname with
  | some tgt => .skip tgt
  | none     => .resolve

/-- New work items spawned by a freshly elaborated elf at `sourceIdx`:
    one per `DT_NEEDED` entry, tagged with the providing object's
    runpath. -/
def workOfElf (sourceIdx : Nat) (elf : Elaborate.Elf) : List WorkItem :=
  elf.needed.toList.map fun n =>
    { soname := n, sourceIdx, runpath := elf.runpath }

-- ============================================================================
-- Characterisation theorems — pin down `dispatch` and `workOfElf` so
-- the driver's invariant proofs can cite them.
-- ============================================================================

/-- `dispatch` returns `.skip tgt` iff `findLoadedIdx` returned `some tgt`. -/
theorem dispatch_skip_iff {objs : Array LoadedObject} {item : WorkItem}
    {tgt : Nat} :
    dispatch objs item = .skip tgt ↔ findLoadedIdx objs item.soname = some tgt := by
  constructor
  · intro h
    unfold dispatch at h
    split at h
    · rename_i tgt' h_find
      injection h with h_tgt; rw [← h_tgt]; exact h_find
    · cases h
  · intro h
    unfold dispatch
    rw [h]

/-- `dispatch` returns `.resolve` iff `findLoadedIdx` returned `none`. -/
theorem dispatch_resolve_iff {objs : Array LoadedObject} {item : WorkItem} :
    dispatch objs item = .resolve ↔ findLoadedIdx objs item.soname = none := by
  constructor
  · intro h
    unfold dispatch at h
    split at h
    · cases h
    · assumption
  · intro h
    unfold dispatch
    rw [h]

/-- The `.skip` arm of `dispatch` carries `tgt < objs.size`, because
    `dispatch` produces `.skip` only when `findLoadedIdx` returned the
    matching index — which is bounded by `findLoadedIdx_lt`. -/
theorem dispatch_skip_tgt_lt {objs : Array LoadedObject}
    {item : WorkItem} {tgt : Nat}
    (h : dispatch objs item = .skip tgt) :
    tgt < objs.size :=
  findLoadedIdx_lt objs item.soname (dispatch_skip_iff.mp h)

/-- `workOfElf` items all carry `sourceIdx = sourceIdx`. Used by the
    state-update helpers to maintain `workSourcesValid` after pushing a
    new object's NEEDED entries onto the queue. -/
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
-- maintained by `BfsState.step` across iterations and lets callers
-- treat every queued source as a valid index without an `Option` dance.
-- ============================================================================

/-- BFS carrier: the accumulating `LoadGraph` plus the pending work
    queue, bundled with the invariant that every queued item's
    `sourceIdx` is in range for the current graph.

    Initial state: `BfsState.initial`. Per-iteration state evolution:
    `BfsState.step`. End state: `work = []` (no more sonames to
    resolve). All transitions preserve `workSourcesValid`, so it
    never has to be re-proven at consumer sites. -/
structure BfsState where
  graph            : LoadGraph
  work             : List WorkItem
  /-- Every queued item's source object exists. Maintained because:
      · `linkExisting` drops the head and doesn't grow objects — tail
        items remain valid because `recordDep` preserves objects.
      · `appendAndQueue` grows objects (so old bounds still hold by
        `<-of-<` monotonicity) and the new `workOfElf` items all carry
        `sourceIdx = newIdx < (g.appendChild …).objects.size`. -/
  workSourcesValid : ∀ item ∈ work, item.sourceIdx < graph.objects.size

namespace BfsState

/-- Initial BFS state: the main object alone (via `LoadGraph.singleton`),
    with its NEEDED entries queued. `workSourcesValid` holds because
    every initial work item has `sourceIdx = 0 < 1 = singleton size`. -/
def initial (mainObj : LoadedObject) : BfsState :=
  let graph := LoadGraph.singleton mainObj
  { graph
    work := workOfElf 0 mainObj.elf
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

-- ============================================================================
-- State-update helpers — one per non-error branch of `step`.
-- Each takes the BFS state plus the tail's bound and produces the next
-- state with `workSourcesValid` re-established locally. This is why
-- `step` itself can stay short.
-- ============================================================================

/-- Record a dep edge to an already-loaded object and drop the head of
    the queue. Used by both branches of `step` that find the target
    already loaded:
      · pre-IO dedup (`.skip` from `dispatch`),
      · post-IO dedup (`findLoadedIdx` on the canonical SONAME).
    `recordDep` doesn't touch `objects`, so the tail bound `h_rest_valid`
    transfers directly into the new state's `workSourcesValid`. -/
def linkExisting (s : BfsState) (srcIdx : Nat) (rest : List WorkItem)
    (h_rest_valid : ∀ i ∈ rest, i.sourceIdx < s.graph.objects.size)
    (tgt : Nat) (h_tgt : tgt < s.graph.objects.size) : BfsState :=
  { graph := s.graph.recordDep srcIdx tgt h_tgt
    work := rest
    workSourcesValid := h_rest_valid }

/-- Append a freshly-discovered object, link it from `srcIdx`, and
    enqueue its NEEDED items. After `appendChild`, `objects.size`
    grows by one: old bounds lift by `Nat.lt_succ_of_lt`; the newly
    enqueued items all carry `sourceIdx = oldSize`, which is `< oldSize + 1`. -/
def appendAndQueue (s : BfsState) (srcIdx : Nat) (rest : List WorkItem)
    (h_rest_valid : ∀ i ∈ rest, i.sourceIdx < s.graph.objects.size)
    (obj : LoadedObject)
    (h_fresh : findLoadedIdx s.graph.objects obj.name = none) : BfsState :=
  let newIdx  := s.graph.objects.size
  let g'      := s.graph.appendChild srcIdx obj h_fresh
  let newWork := workOfElf newIdx obj.elf
  have h_g_size : g'.objects.size = s.graph.objects.size + 1 :=
    LoadGraph.appendChild_size _ _ _ _
  { graph := g'
    work  := rest ++ newWork
    workSourcesValid := by
      intro i hi
      rw [h_g_size]
      rcases List.mem_append.mp hi with hL | hR
      · exact Nat.lt_succ_of_lt (h_rest_valid i hL)
      · rw [workOfElf_sourceIdx newIdx obj.elf hR]; exact Nat.lt_succ_self _ }

-- ============================================================================
-- step — one BFS iteration. With the per-branch helpers extracted, the
-- body is just dispatch → call the matching helper.
-- ============================================================================

/-- Result of one BFS iteration: either the queue was empty (`done`,
    `s.graph` is the final output) or one item was processed
    (`continue s'`, with `s'.workSourcesValid` preserved). -/
inductive StepResult where
  | done
  | continue (s' : BfsState)

/-- Process exactly one work item.

    Returns `.done` if the queue is empty (terminal state — caller
    should return `s.graph`). Otherwise dispatches the head via the
    pure `dispatch` and one of three branches:

    · `.skip` — pre-IO dedup hit. `linkExisting` records the edge.
    · `.resolve` + post-IO dedup hit — SONAME canonicalisation
      collapsed two NEEDED strings to one object. `linkExisting` again.
    · `.resolve` + new object — `appendAndQueue` pushes the object
      and enqueues its NEEDED items.

    Called as `s.step eff` via dot notation. -/
def step {m : Type → Type} [Monad m] (s : BfsState) (eff : Effects m) :
    m StepResult := do
  match h_work : s.work with
  | [] => pure .done
  | item :: rest =>
    have h_rest_valid : ∀ i ∈ rest, i.sourceIdx < s.graph.objects.size :=
      fun i hi => s.workSourcesValid i (by rw [h_work]; exact List.mem_cons_of_mem _ hi)
    match h_step : dispatch s.graph.objects item with
    | .skip tgt =>
      pure (.continue (s.linkExisting item.sourceIdx rest h_rest_valid
        tgt (dispatch_skip_tgt_lt h_step)))
    | .resolve =>
      match ← eff.resolveDep item.soname item.runpath with
      | none =>
        eff.fail s!"discover: cannot find '{item.soname}' \
          (runpath={item.runpath})"
      | some (canonical, handle, elf) =>
        match h_idx : findLoadedIdx s.graph.objects canonical with
        | some tgt =>
          pure (.continue (s.linkExisting item.sourceIdx rest h_rest_valid
            tgt (findLoadedIdx_lt _ _ h_idx)))
        | none =>
          let obj : LoadedObject := { name := canonical, handle, elf }
          pure (.continue (s.appendAndQueue item.sourceIdx rest h_rest_valid
            obj h_idx))

end BfsState

-- ============================================================================
-- discoverLoopWith — iterate `BfsState.step` until the queue empties
-- (or fuel runs out). The fuel cap is invisible in practice; each
-- push monotonically grows `objects.size`, and `objects.size ≤ total
-- transitive deps in the system`.
-- ============================================================================

/-- Drive the BFS to completion using the given effects. Returns
    `s.graph` once the work queue empties. The fuel cap is a Lean-
    termination concession — the natural termination (queue shrinks
    to empty) is invisible to the type system. -/
def discoverLoopWith {m : Type → Type} [Monad m] (eff : Effects m)
    (fuel : Nat) (s : BfsState) : m LoadGraph := do
  match fuel with
  | 0 => pure s.graph
  | fuel + 1 =>
    match ← s.step eff with
    | .done => pure s.graph
    | .continue s' => discoverLoopWith eff fuel s'

end LeanLoad.Discover

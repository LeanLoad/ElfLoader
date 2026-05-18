/-
BFS state machine — per-item dispatch.

`WorkItem` is one queued `DT_NEEDED` lookup; `dispatch` decides
whether to skip (already loaded) or to resolve (defer to the IO
seam). `dispatch` is a pure function over `(g, item)`; the queue
+ monadic effects live in `BfsState.step` (`Discover/BFS.lean`).

`workOfElf` is the producer: given a freshly elaborated `Elf` and its
sourceIdx in the graph, it enumerates the per-NEEDED `WorkItem`s to
push onto the queue.

Characterisation theorems (`dispatch_skip_iff`, `dispatch_resolve_iff`,
`dispatch_skip_tgt_lt`, `workOfElf_sourceIdx`) pin down the decision
so `BfsState.step`'s invariant maintenance can cite them by name.
-/

import LeanLoad.Discover.Graph

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
    loaded in `g`. Returns the matching index for the `.skip` branch's
    edge recording. The `.done` case (empty work queue) is handled by
    the caller — `dispatch` is only invoked on a concrete item. -/
def dispatch (g : LoadGraph) (item : WorkItem) : Decision :=
  match g.findLoadedIdx item.soname with
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
-- `BfsState.step`'s invariant proofs can cite them.
-- ============================================================================

/-- `dispatch` returns `.skip tgt` iff `findLoadedIdx` returned `some tgt`.
    Each branch is a direct match — useful for tests that want to
    assert which branch fires on a given input. -/
theorem dispatch_skip_iff {g : LoadGraph} {item : WorkItem} {tgt : Nat} :
    dispatch g item = .skip tgt ↔ g.findLoadedIdx item.soname = some tgt := by
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
theorem dispatch_resolve_iff {g : LoadGraph} {item : WorkItem} :
    dispatch g item = .resolve ↔ g.findLoadedIdx item.soname = none := by
  constructor
  · intro h
    unfold dispatch at h
    split at h
    · cases h
    · assumption
  · intro h
    unfold dispatch
    rw [h]

/-- The `.skip` arm of `dispatch` carries `tgt < g.objects.size`, because
    `dispatch` produces `.skip` only when `findLoadedIdx` returned the
    matching index — which is bounded by `findLoadedIdx_lt`. -/
theorem dispatch_skip_tgt_lt {g : LoadGraph}
    {item : WorkItem} {tgt : Nat}
    (h : dispatch g item = .skip tgt) :
    tgt < g.objects.size :=
  g.findLoadedIdx_lt item.soname (dispatch_skip_iff.mp h)

/-- `workOfElf` items all carry `sourceIdx = sourceIdx`. Used by
    `BfsState.step` to maintain the BFS-state invariant after pushing
    a new object's NEEDED entries onto the queue. -/
theorem workOfElf_sourceIdx (sourceIdx : Nat) (elf : Elaborate.Elf)
    {item : WorkItem} (h_mem : item ∈ workOfElf sourceIdx elf) :
    item.sourceIdx = sourceIdx := by
  unfold workOfElf at h_mem
  rw [List.mem_map] at h_mem
  obtain ⟨_, _, h_eq⟩ := h_mem
  rw [← h_eq]

end LeanLoad.Discover

/-
BFS state machine — per-item dispatch.

`WorkItem` is one queued `DT_NEEDED` lookup; `step` decides whether
to skip (already loaded) or to resolve (call out to IO). The queue
itself is managed by `bfsStep1` in `Discover.BFS`; `step` only sees
one item at a time.

`workOfElf` is the producer: given a freshly elaborated `Elf` and its
sourceIdx in the graph, it enumerates the per-NEEDED `WorkItem`s to
push onto the queue.

Characterisation theorems (`step_skip_iff`, `step_resolve_iff`,
`step_skip_tgt_lt`, `workOfElf_sourceIdx`) pin down the decision so
`bfsStep1`'s invariant maintenance can cite them by name.
-/

import LeanLoad.Discover.Graph

namespace LeanLoad.Discover

open LeanLoad

-- ============================================================================
-- WorkItem + StepResult + step.
-- ============================================================================

/-- One BFS work item: a `DT_NEEDED` soname, with its source-object
    context. `sourceIdx` identifies the object whose `DT_NEEDED`
    produced this item — `bfsStep1` records the dep edge once the
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

-- ============================================================================
-- Characterisation theorems — pin down `step` and `workOfElf` so
-- `bfsStep1`'s invariant proofs can cite them.
-- ============================================================================

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

end LeanLoad.Discover

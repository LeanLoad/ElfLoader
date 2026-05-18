/-
BFS driver — generic over the effect monad.

The state carrier (`BfsState`) bundles the accumulating `LoadGraph`
with the pending work queue and one structural invariant
(`workSourcesValid`: every queued item's `sourceIdx` is a valid
object index). `BfsState.step` advances the state by one work item;
`discoverLoopWith` iterates to completion.

Effects are abstract — `Effects (m : Type → Type)` is a record
bundling `resolveDep` (open + parse + elaborate) and `fail` (surface
a fatal error). Production wires `Effects.io` over `IO` in
`Discover/IO.lean`; tests wire `Effects.test` over `Except String` in
`Discover/Test.lean`. Same driver, two effects.
-/

import LeanLoad.Discover.Step

namespace LeanLoad.Discover

open LeanLoad

-- ============================================================================
-- BfsState — the BFS carrier with one structural invariant: every
-- pending work item's `sourceIdx` is a valid object index. This is
-- maintained by `BfsState.step` across iterations and lets callers
-- treat every queued source as a `Fin graph.objects.size` without
-- an `Option` dance.
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
      · `.skip` / `.resolve-dedup-hit` drop the head and don't grow
        objects — tail items remain valid by record-projection.
      · `.resolve-new` grows objects (so old bounds still hold by
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

end BfsState

-- ============================================================================
-- Effects — abstract IO leaves so `BfsState.step` is generic over the
-- effect monad. Production: `IO` via `Effects.io` (defined in
-- `Discover/IO.lean`). Tests: synthetic monad over an in-memory
-- store via `Effects.test` (in `Discover/Test.lean`).
-- ============================================================================

/-- The single IO leaf `BfsState.step` calls, plus a `fail` for the
    missing-dep error. Parameterised over the effect monad `m` so
    tests can swap in a pure `Except String` (or `ReaderT TestStore`)
    instance.

    The search-path arguments (`LD_LIBRARY_PATH`) are *not* passed
    through here — the production `Effects.io` reads them inside the
    C runtime (`Runtime.openByName`). Tests construct their own
    `Effects.test` that closes over whatever environment they want
    to simulate. -/
structure Effects (m : Type → Type) where
  /-- Resolve a `DT_NEEDED` soname against the runtime's search rules
      (env + runpath), open the file, parse it, and elaborate. Returns:
      · `none` — soname didn't resolve to an existing file (missing dep).
      · `some (name, handle, elf)` — `name` is the canonical dedup key
        (`DT_SONAME` if set, else the requested NEEDED string), `handle`
        is the open fd (kept for downstream `mmap`), `elf` is the
        elaborated view.
      Parse/elaborate failures escape via the monad's error mechanism
      (IO exception in production; `throw` in `Except`-based tests).
      Splitting "not found" out as a `none` instead of using `fail`
      lets `BfsState.step` produce the diagnostic with the full
      `WorkItem` context (runpath, soname) attached. -/
  resolveDep : String → Option String →
               m (Option (String × Runtime.FileHandle × Elaborate.Elf))
  /-- Surface a fatal error. In `IO`, this is `throw (IO.userError …)`;
      in `Except String`, it's `throw`. Polymorphic in the return type
      because the caller is in continuation position. -/
  fail       : {α : Type} → String → m α

namespace BfsState

-- ============================================================================
-- BfsState.step — one BFS iteration. Pure interface, generic over `m`,
-- consumes/produces `BfsState` so the invariant is type-enforced
-- across steps. The driver `discoverLoopWith` just iterates this.
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
    pure `Discover.step` and one of three branches:

    · `.skip` — soname already loaded. Edge recorded via
      `LoadGraph.recordDep`, queue tail unchanged.
    · `.resolve` + post-canonicalisation dedup hit — drop the
      re-parsed object, record edge to existing index.
    · `.resolve` + new object — push via `LoadGraph.appendChild`,
      enqueue the new elf's NEEDED entries via `workOfElf`.

    In each branch, `workSourcesValid` is re-established from the
    pre-existing invariant plus locally available bounds.

    Called as `s.step eff` via dot notation. -/
def step {m : Type → Type} [Monad m] (s : BfsState) (eff : Effects m) :
    m StepResult := do
  match h_work : s.work with
  | [] => pure .done
  | item :: rest =>
    -- The invariant gives us bounds on every queued item, including
    -- those still in `rest` (which we'll re-queue or drop).
    have h_rest_valid : ∀ i ∈ rest, i.sourceIdx < s.graph.objects.size := by
      intro i hi
      exact s.workSourcesValid i (by rw [h_work]; exact List.mem_cons_of_mem _ hi)
    match h_step : Discover.step s.graph.objects item with
    | .skip tgt =>
      have h_tgt : tgt < s.graph.objects.size := step_skip_tgt_lt h_step
      let g' := s.graph.recordDep item.sourceIdx tgt h_tgt
      -- recordDep_size: g'.objects.size = s.graph.objects.size (rfl), so
      -- tail bounds carry over verbatim.
      pure (.continue { graph := g', work := rest, workSourcesValid := h_rest_valid })
    | .resolve =>
      match ← eff.resolveDep item.soname item.runpath with
      | none =>
        eff.fail s!"discover: cannot find '{item.soname}' \
          (runpath={item.runpath})"
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

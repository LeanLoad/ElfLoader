/-
LoadGraph — the typed output of Discover.

Loaded objects (`[0] = main`; the rest in an implementation-defined
order), their dep edges, the DFS post-order init sequence, and seven
structural invariants:

  · `sizePos`        — `0 < objects.size`. Makes `main` total (no Option).
  · `namesNodup`     — names pairwise distinct (canonical-SONAME dedup).
  · `depsSize`       — `deps.size = objects.size`. `deps` parallel.
  · `depsBounds`     — every recorded edge target is a valid object idx.
  · `closure`        — `∀ i, deps[i].size = objects[i].elf.needed.size`.
                       Every NEEDED has been discovered, resolved, and
                       recorded — downstream sees a complete dep relation.
  · `initOrderSize`  — `initOrder.size = objects.size`. Every object
                       appears exactly once in the init sequence.
  · `initOrderNodup` — no duplicate `.val`s. With `initOrderSize`, makes
                       `initOrder` a permutation of `[0, objects.size)`.

`LoadGraph` is the *output* type of Discover and the canonical spec of
what Discover produces. Construction lives in `Discover/Driver.lean`
on an internal `DfsState` (carries the four "structural" invariants
plus a name→index HashMap accelerator, a pending counter for closure,
and the postOrder array). The output invariants `closure`,
`initOrderSize`, `initOrderNodup` are established at the end of
`discoverWith` from `DfsState`'s end-state.

File layout:
  · `LoadedObject` + `ofMain` — one entry of the graph.
  · `LoadGraph` + `LoadGraph.main` — the bundled output.
  · `recordEdge` + lemmas — `Array (Array Nat)` push primitive used by
    `DfsState.recordDep`.
  · `findLoadedIdx` + lemmas — name-based lookup over `Array
    LoadedObject`. Free function so `DfsState` can use it.
-/

import LeanLoad.Parse.RawElf
import LeanLoad.Elaborate.Elf
import LeanLoad.Runtime

namespace LeanLoad.Discover

open LeanLoad
open LeanLoad.Parse

-- ============================================================================
-- LoadedObject — one entry of the graph.
-- ============================================================================

/-- One loaded object. Production policy (`Discover/IO.lean`):
    NEEDED-loaded deps must have `DT_SONAME` (used as `.name`);
    the main executable's `.name` is `basename mainPath` (executables
    conventionally don't set SONAME). -/
structure LoadedObject where
  /-- Canonical dedup key. For NEEDED deps: `elf.soname.get!` (production
      requires DT_SONAME). For the main executable: `basename mainPath`. -/
  name : String
  /-- Open read-only file handle, kept for `pread` (parsing extras) and
      `mmap` (Materialize stage). Production paths always carry a real
      fd; tests use a dummy `(0 : UInt32)`. -/
  handle : Runtime.FileHandle
  /-- Elaborated ELF — output of `Elaborate.elaborate` after `Parse.parse`.
      The type is the witness that PT_LOAD well-formedness held and every
      dynamic relocation was located against a covering segment. -/
  elf  : Elaborate.Elf

/-- Construct the main `LoadedObject` from a user-supplied path. The
    canonical name is the path basename — executables don't conventionally
    set DT_SONAME, and main is path-loaded (not NEEDED-driven), so we
    don't consult `elf.soname`. -/
def LoadedObject.ofMain (mainPath : String) (handle : Runtime.FileHandle)
    (elf : Elaborate.Elf) : LoadedObject :=
  { name := (mainPath.splitOn "/").getLast?.getD mainPath, handle, elf }

-- ============================================================================
-- LoadGraph — the bundled output of Discover.
-- ============================================================================

/-- Output of `Discover` — every transitively-NEEDED object loaded,
    indexed for `Fin`-total downstream access, with the dep graph and
    a DFS post-order init sequence bundled. The specific *traversal*
    order Discover used is an implementation detail: only `[0] = main`
    is spec-relevant. Symbol resolution (gabi 08 § Shared Object
    Dependencies) iterates BFS-from-0 over `deps` — see
    `Plan.Resolve.bfsOrder` — and doesn't depend on `objects`'s
    intrinsic order.

    See the module docstring for the seven invariants. -/
structure LoadGraph where
  /-- The loaded objects, indexed in an implementation-defined order
      whose only spec-relevant property is `objects[0] = main` (the
      `Discover` seed). Consumers that need a particular traversal
      order compute it explicitly from `deps` — e.g. BFS for symbol
      resolution (`Plan.Resolve.bfsOrder`), DFS post-order for init
      (already bundled as `initOrder`). -/
  objects     : Array LoadedObject
  /-- Per-object dependency indices, recorded during DFS. Parallel to
      `objects` and complete: every NEEDED has been resolved to an
      idx in `deps[i]`. -/
  deps        : Array (Array Nat)
  /-- DFS post-order over the dep graph: indices in the order each
      object's `dfs` returned. Used as the init order (deps before
      dependents, cycles undefined per gabi 08). Established during
      `discoverWith` via `DfsState.markComplete`. -/
  initOrder   : Array (Fin objects.size)
  /-- Non-emptiness — witnessed by `DfsState.initial` seeding with main
      before the DFS begins. -/
  sizePos     : 0 < objects.size
  /-- Names pairwise distinct. Witnessed by the DFS `nameIx` dedup
      check before each push. -/
  namesNodup  : (objects.map (·.name)).toList.Nodup
  /-- `deps` is parallel to `objects`. -/
  depsSize    : deps.size = objects.size
  /-- Every recorded edge target is a valid index into `objects`. -/
  depsBounds  : ∀ (i : Nat) (h : i < deps.size), ∀ t ∈ deps[i], t < objects.size
  /-- Closure under NEEDED: every object's `deps` row holds exactly one
      entry per `DT_NEEDED` of its elf. Established at the end of
      `discoverWith` once the top-level DFS has returned. -/
  closure     : ∀ (i : Nat) (h : i < objects.size),
    (deps[i]'(by rw [depsSize]; exact h)).size = (objects[i]'h).elf.needed.size
  /-- `initOrder` is parallel to `objects` — every object appears
      exactly once. -/
  initOrderSize  : initOrder.size = objects.size
  /-- No duplicate indices in `initOrder` (treated as `Nat` via `.val`).
      Combined with `initOrderSize`, makes `initOrder` a permutation
      of `[0, objects.size)`. -/
  initOrderNodup : (initOrder.toList.map (·.val)).Nodup

namespace LoadGraph

/-- The main executable — total because `LoadGraph` carries `sizePos`. -/
def main (g : LoadGraph) : LoadedObject := g.objects[0]'g.sizePos

/-- Single-step dependency edge in the loaded graph: `j ∈ deps[i]`.
    Defined on `Nat × Nat`; the `i < g.deps.size` hypothesis is part
    of the existential so the relation can be lifted through
    `Reachable` without a Fin wrapper. -/
def Step (g : LoadGraph) (i j : Nat) : Prop :=
  ∃ (h : i < g.deps.size), j ∈ g.deps[i]'h

/-- Reachable from `i` to `j` via dep edges (reflexive-transitive
    closure of `Step`). Spec witness for the gabi 08 § Shared Object
    Dependencies "dependency graph" — every NEEDED chain from main is
    a path under this relation. -/
inductive Reachable (g : LoadGraph) : Nat → Nat → Prop
  /-- Every node is reachable from itself in zero steps. -/
  | refl (i : Nat) : Reachable g i i
  /-- Extending a reachability path by one edge. -/
  | tail {i j k : Nat} (h_ij : Reachable g i j) (h_jk : g.Step j k) :
      Reachable g i k

/-- Reachable from main (idx 0). Convenience for the most common case. -/
def ReachableFromMain (g : LoadGraph) (i : Nat) : Prop :=
  g.Reachable 0 i

end LoadGraph

-- ============================================================================
-- recordEdge — push a target onto deps[src]. Used by `DfsState.recordDep`.
-- ============================================================================

/-- Add an out-edge `src → tgt` to `deps`. `Array.modify` returns the
    array unchanged when `src` is out of range, but in practice every
    `src` we pass is a known-valid object index (the DFS only ever uses
    the index of an object that's already been pushed). -/
def recordEdge (deps : Array (Array Nat)) (src tgt : Nat) :
    Array (Array Nat) :=
  deps.modify src (·.push tgt)

theorem recordEdge_size (deps : Array (Array Nat)) (src tgt : Nat) :
    (recordEdge deps src tgt).size = deps.size := by
  unfold recordEdge; exact Array.size_modify

/-- Per-row size accounting: `recordEdge` grows row `src` by one and
    leaves every other row's size unchanged. Used by the DFS closure
    proof to track per-row edge growth across the foldlM over
    `elf.needed`. -/
theorem recordEdge_row_size {deps : Array (Array Nat)} {src tgt i : Nat}
    (h : i < deps.size) :
    ((recordEdge deps src tgt)[i]'(by rw [recordEdge_size]; exact h)).size =
      deps[i].size + (if src = i then 1 else 0) := by
  have h_get :
      (recordEdge deps src tgt)[i]'(by rw [recordEdge_size]; exact h) =
        if src = i then deps[i].push tgt else deps[i] := by
    unfold recordEdge
    exact Array.getElem_modify _
  rw [h_get]
  by_cases h_eq : src = i
  · simp [h_eq, Array.size_push]
  · simp [h_eq]

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
-- findLoadedIdx — name lookup over Array LoadedObject. Free function so
-- both `LoadGraph` (final output) and `DfsState` (Driver.lean
-- construction state) can use it.
-- ============================================================================

/-- Linear search for an object by name. Defined via `Array.findIdx?`
    so the size bound (`findLoadedIdx_lt` below) drops out of the core
    `Array.of_findIdx?_eq_some` characterisation. -/
def findLoadedIdx (objects : Array LoadedObject) (name : String) : Option Nat :=
  objects.findIdx? (·.name == name)

/-- The index returned by `findLoadedIdx` is `< objects.size`. -/
theorem findLoadedIdx_lt {objects : Array LoadedObject} {name : String} {idx : Nat}
    (h : findLoadedIdx objects name = some idx) : idx < objects.size := by
  have h_match :=
    Array.of_findIdx?_eq_some (xs := objects) (p := (·.name == name)) h
  match h_get : objects[idx]? with
  | some _ =>
    obtain ⟨h_lt, _⟩ := Array.getElem?_eq_some_iff.mp h_get
    exact h_lt
  | none =>
    rw [h_get] at h_match
    exact absurd h_match (by simp)

/-- `findLoadedIdx = none` characterised: no object in `objects` carries
    the given name. -/
theorem findLoadedIdx_none_iff (objects : Array LoadedObject) (name : String) :
    findLoadedIdx objects name = none ↔ ∀ o ∈ objects, o.name ≠ name := by
  unfold findLoadedIdx
  rw [Array.findIdx?_eq_none_iff]
  simp

/-- Pushing a freshly-resolved object preserves the names-Nodup invariant.
    The precondition `findLoadedIdx = none` is what `DfsState.pushObject`
    discharges from `nameIx[obj.name]? = none` via `nameIxValid`. -/
theorem nodup_names_push_of_findLoadedIdx_none
    {objects : Array LoadedObject} {obj : LoadedObject}
    (h_nodup : (objects.map (·.name)).toList.Nodup)
    (h_fresh : findLoadedIdx objects obj.name = none) :
    ((objects.push obj).map (·.name)).toList.Nodup := by
  rw [Array.map_push, Array.toList_push, List.nodup_append]
  refine ⟨h_nodup, by simp, ?_⟩
  intro a ha b hb hab
  rw [List.mem_singleton] at hb
  subst hb
  obtain ⟨o, ho_mem, ho_name⟩ := Array.mem_map.mp (Array.mem_toList_iff.mp ha)
  have h_ne : o.name ≠ obj.name :=
    (findLoadedIdx_none_iff objects obj.name).mp h_fresh o ho_mem
  exact h_ne (ho_name.trans hab)

end LeanLoad.Discover

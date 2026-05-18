/-
LoadGraph + invariant-bundling methods.

The output type of Discover and the BFS state's primary carrier:
loaded objects (in BFS order, main at idx 0), dep edges, and four
structural invariants the rest of the loader depends on (non-emptiness,
name-Nodup, deps-shape, deps-bounds).

Two construction methods (`recordDep`, `appendChild`) bundle the
invariant maintenance so the BFS driver (`BfsState.step`) only calls them
— no inline proof boilerplate at the recursive call sites.

File layout:
  · LoadedObject — one entry of the graph (name + handle + elf).
  · Pure dedup primitives + soundness — `findLoadedIdx` plus the
    `nodup_names_push_…` lemma `appendChild` consumes.
  · Edge accumulation — `recordEdge` + size/bounds preservation.
  · LoadGraph + `main` / `recordDep` / `appendChild` + characterisation
    theorems (`recordDep_objects`, `appendChild_size`, etc.).
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
      requires DT_SONAME). For the main executable: `basename
      mainPath`. -/
  name : String
  /-- Open read-only file handle, kept for `pread` (parsing extras)
      and `mmap` (Materialize stage). Production paths always carry a
      real fd; tests use a dummy `(0 : UInt32)`. -/
  handle : Runtime.FileHandle
  /-- Elaborated ELF — output of `Elaborate.elaborate` after
      `Parse.parse`. The type itself is the witness that PT_LOAD
      well-formedness held and every dynamic relocation was located
      against a covering segment. -/
  elf  : Elaborate.Elf

/-- Construct the main `LoadedObject` from a user-supplied path. The
    canonical name is the path basename — executables don't
    conventionally set DT_SONAME, and main is path-loaded (not
    NEEDED-driven), so we don't consult `elf.soname`. -/
def LoadedObject.ofMain (mainPath : String) (handle : Runtime.FileHandle)
    (elf : Elaborate.Elf) : LoadedObject :=
  { name := (mainPath.splitOn "/").getLast?.getD mainPath, handle, elf }

-- ============================================================================
-- Pure dedup primitives.
--
-- The BFS uses `findLoadedIdx` to both dedup (none → not loaded) and
-- (in the `.skip` arm) recover the matching index for edge recording.
-- The dedup *key* for each `LoadedObject` is its `.name`, computed by
-- the IO seam (`Effects.resolveDep`) from `DT_SONAME` — see
-- `Discover/IO.lean` for the production policy.
-- ============================================================================

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
    The precondition `findLoadedIdx = none` is what `BfsState.step` discharges
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
        mismatch between `DT_NEEDED` strings and `DT_SONAME`-canonical
        names. `Init.order` consumes this directly — no name-based
        re-derivation, no silent drops.

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

/-- The singleton graph: one object, no edges, all invariants trivial.
    Used as the BFS seed (`BfsState.initial`) — keeps the four-
    invariant boilerplate co-located with the other LoadGraph
    constructors instead of leaking through the abstraction barrier. -/
def singleton (obj : LoadedObject) : LoadGraph :=
  { objects    := #[obj]
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

@[simp] theorem singleton_objects (obj : LoadedObject) :
    (singleton obj).objects = #[obj] := rfl

/-- The main executable — total because `LoadGraph` carries the
    non-emptiness witness. -/
def main (g : LoadGraph) : LoadedObject := g.objects[0]'g.sizePos

/-- Record a dep edge `src → tgt` to an already-loaded object. The
    target's bound is the caller's obligation — `BfsState.step` discharges
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

end LeanLoad.Discover

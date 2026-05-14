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

      * `depsSize` — `deps.size = val.size`. Maintained by every push.

      * `depsBounds` — every recorded edge target is a valid index
        into `val`. Maintained because edges only originate from
        `findLoadedIdx` (iterates `[:objs.size]`) or from the index
        about to be pushed (always `< objs.size + 1`).

    Access pattern: callers peel via `g.val` to use Array methods
    (`g.val.size`, `g.val[i]?`, `for obj in g.val do`). Use `g.main`
    whenever main is what you want, not `g.val[0]?`. -/
structure LoadGraph where
  /-- The loaded objects, in BFS discovery order. Main at index 0. -/
  val        : Array LoadedObject
  /-- Per-object dependency indices, recorded during BFS. -/
  deps       : Array (Array Nat)
  /-- Non-emptiness — `0 < val.size`. Witnessed by `discover` seeding
      with `main` before entering the BFS loop. -/
  sizePos    : 0 < val.size
  /-- Names pairwise distinct. Witnessed by the BFS `alreadyLoaded`
      dedup check. -/
  namesNodup : (val.map (·.name)).toList.Nodup
  /-- `deps` is parallel to `val`. -/
  depsSize   : deps.size = val.size
  /-- Every recorded edge target is a valid index. -/
  depsBounds : ∀ (i : Nat) (h : i < deps.size), ∀ t ∈ deps[i], t < val.size

namespace LoadGraph

/-- The main executable — total because `LoadGraph` carries the
    non-emptiness witness. -/
def main (g : LoadGraph) : LoadedObject := g.val[0]'g.sizePos

end LoadGraph

-- ============================================================================
-- Pure helpers
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

-- ============================================================================
-- Plan: per-step decision + state integration
-- ============================================================================

/-- One BFS work item: a `DT_NEEDED` soname, with its `(sourceIdx, runpath)`
    context — `sourceIdx` identifies the object whose `DT_NEEDED` produced
    this item (so `discoverLoop` can record the dep edge once the target
    is resolved); `runpath` carries the source's `DT_RUNPATH` for
    search-path resolution. -/
abbrev WorkItem := Nat × Option String × String

/-- The result of one BFS step over `(objs, work)`. -/
inductive StepResult where
  /-- Work queue empty: discovery is complete. -/
  | done
  /-- Soname already loaded: drop the work item, but record the dep
      edge `sourceIdx → targetIdx`. -/
  | skip (sourceIdx targetIdx : Nat) (rest : List WorkItem)
  /-- Soname is new: needs IO to resolve to a path, open, and parse,
      then `integrate` the parsed result. -/
  | resolve (sourceIdx : Nat) (sn : String) (rp : Option String)
            (rest : List WorkItem)

/-- Pure step: examine the work queue's head and decide what to do.
    The dedup check uses `findLoadedIdx` (returns the matching index
    for the `.skip` branch's edge recording). -/
def step (objs : Array LoadedObject) (work : List WorkItem) : StepResult :=
  match work with
  | []                  => .done
  | (src, rp, sn) :: rest =>
    match findLoadedIdx objs sn with
    | some tgt => .skip src tgt rest
    | none     => .resolve src sn rp rest

/-- New work items spawned by a freshly elaborated elf at `sourceIdx`:
    one per `DT_NEEDED` entry, tagged with the providing object's
    runpath. -/
def workOfElf (sourceIdx : Nat) (elf : Elaborate.Elf) : List WorkItem :=
  elf.needed.toList.map (fun n => (sourceIdx, elf.runpath, n))

-- ============================================================================
-- Soundness theorems for the BFS dedup primitive.
-- ============================================================================

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
    the invariant. -/
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

end LeanLoad.Discover

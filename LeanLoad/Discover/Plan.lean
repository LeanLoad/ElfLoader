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
    with `main` at index 0. The non-emptiness witness is in the type:
    `Discover.discover` always seeds with main, and BFS only ever
    pushes (never removes), so `0 < g.val.size` holds by construction.
    Encoding the invariant in the type makes `g.main` total (no
    `Option`) and removes the "what if there's no main" defensive
    code from every consumer.

    Access pattern: callers peel via `g.val` to use Array methods
    (`g.val.size`, `g.val[i]?`, `for obj in g.val do`). The subtype
    layer is purposefully visible — every `.val` is a reminder that
    we're stripping a load-bearing invariant. Use `g.main` whenever
    main is what you want, not `g.val[0]?`.

    Dep edges are *not* stored. The only downstream consumer is
    `LeanLoad.Init.computeOrder` (init/fini), which re-derives them
    from `obj.elf.needed`. -/
abbrev ObjectList := { a : Array LoadedObject //
  0 < a.size ∧ (a.map (·.name)).toList.Nodup }

namespace ObjectList

/-- Non-emptiness witness — the first half of `ObjectList.property`. -/
def sizePos (g : ObjectList) : 0 < g.val.size := g.property.1

/-- Names of the loaded objects are pairwise distinct — the second
    half of `ObjectList.property`. Used by `Init.buildDeps` to argue
    the `name → index` map is injective. -/
def namesNodup (g : ObjectList) : (g.val.map (·.name)).toList.Nodup := g.property.2

/-- The main executable — total because the subtype carries the
    non-emptiness witness. -/
def main (g : ObjectList) : LoadedObject := g.val[0]'g.sizePos

end ObjectList

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
    `DT_NEEDED` entry, and a second time after canonicalisation.
    Soundness lemma: `alreadyLoaded_iff` in `Thm.Discover`. -/
def alreadyLoaded (objs : Array LoadedObject) (name : String) : Bool :=
  objs.any (·.name == name)

-- ============================================================================
-- Plan: per-step decision + state integration
-- ============================================================================

/-- One BFS work item: a `DT_NEEDED` soname, with the runpath of the
    object that referenced it (used during search-path resolution). -/
abbrev WorkItem := Option String × String

/-- The result of one BFS step over `(objs, work)`. -/
inductive StepResult where
  /-- Work queue empty: discovery is complete. -/
  | done
  /-- Soname already loaded (by pre-resolve dedup): drop and continue. -/
  | skip (rest : List WorkItem)
  /-- Soname is new: needs IO to resolve to a path, open, and parse,
      then `integrate` the parsed result. -/
  | resolve (sn : String) (rp : Option String) (rest : List WorkItem)

/-- Pure step: examine the work queue's head and decide what to do. -/
def step (objs : Array LoadedObject) (work : List WorkItem) : StepResult :=
  match work with
  | []              => .done
  | (rp, sn) :: rest =>
    if alreadyLoaded objs sn then .skip rest
    else .resolve sn rp rest

/-- New work items spawned by a freshly elaborated elf: one per
    `DT_NEEDED` entry, tagged with the providing object's runpath. -/
def workOfElf (elf : Elaborate.Elf) : List WorkItem :=
  elf.needed.toList.map (fun n => (elf.runpath, n))

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

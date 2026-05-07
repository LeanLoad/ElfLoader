/-
Discover planner — pure.

The graph-construction logic plus the search-path resolution rules,
separated from the IO loop. Given the current `(objs, work)` state,
decides what to do next; given a just-parsed dep, integrates it. No
file IO, no parsing — those live in `DiscoverApply`.

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

import LeanLoad.Parse.File
import LeanLoad.Runtime

namespace LeanLoad.Discover

open LeanLoad
open LeanLoad.Parse

-- ============================================================================
-- Search-path resolution (pure helpers, used by `DiscoverApply.resolveSoname`)
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
    by the `DT_NEEDED` string we resolved through), and by the file
    path we read it from. -/
structure LoadedObject where
  /-- Canonical name (`DT_SONAME` if defined; otherwise the path
      basename or the resolving `DT_NEEDED` string). Used for
      deduplication. -/
  name : String
  /-- Filesystem path the bytes came from. -/
  path : String
  /-- Open read-only file handle, kept for `pread` (parsing extras)
      and `mmap` (Map stage). `none` for synthetic objects built by
      `LeanLoad.Fixtures` that have no backing file. -/
  handle : Option Runtime.FileHandle := none
  /-- Parsed ELF. -/
  elf  : File.ParsedElf
  /-- Parse-time well-formedness witness on `elf`'s PT_LOAD segments
      (sortedness, file/mem sizing, alignment, gabi-07 congruence,
      raw non-overlap). `Parse.File.parse` constructs this via
      `Parse.Segment.WellFormedB`; synthetic ELFs in `Fixtures` get
      it for free via `decide` (their phdrs are empty, so the
      predicate is vacuously true). -/
  elf_wf : Parse.Segment.WellFormed (Parse.Segment.fromPhdrs elf.phdrs) := by decide

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
abbrev ObjectList := { a : Array LoadedObject // 0 < a.size }

namespace ObjectList

/-- The main executable — total because the subtype carries the
    non-emptiness witness. -/
def main (g : ObjectList) : LoadedObject := g.val[0]'g.property

end ObjectList

-- ============================================================================
-- Pure helpers
-- ============================================================================

/-- The canonical name we use to deduplicate a parsed ELF. Prefer
    `DT_SONAME`; fall back to the original `DT_NEEDED` string. -/
def canonicalName (needed : String) (elf : File.ParsedElf) : String :=
  elf.soname.getD needed

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

/-- Pure integration: given a freshly resolved + parsed dep, update
    `(objs, work)`. Performs the *post-canonicalisation* dedup
    (`canonicalName` may differ from the soname we resolved through);
    a hit returns the unchanged state.

    Takes the parsed-ELF + witness as a single subtype so the
    `LoadedObject.elf_wf` field is total at construction. -/
def integrate (objs : Array LoadedObject) (rest : List WorkItem)
    (sn : String) (path : String) (handle : Runtime.FileHandle)
    (parsed : { elf : File.ParsedElf //
                Parse.Segment.WellFormed (Parse.Segment.fromPhdrs elf.phdrs) }) :
    Array LoadedObject × List WorkItem :=
  let canonical := canonicalName sn parsed.val
  if alreadyLoaded objs canonical then
    (objs, rest)
  else
    let obj : LoadedObject :=
      { name := canonical, path, handle := some handle,
        elf := parsed.val, elf_wf := parsed.property }
    let newPairs : List WorkItem :=
      parsed.val.needed.toList.map (fun n => (parsed.val.runpath, n))
    (objs.push obj, rest ++ newPairs)

/-- `integrate` only ever pushes (or no-ops); preserves the
    `0 < .size` lower bound that `ObjectList` carries. Used by
    `discoverLoop` to thread the non-emptiness invariant. -/
theorem integrate_size_pos (objs : Array LoadedObject) (rest : List WorkItem)
    (sn : String) (path : String) (handle : Runtime.FileHandle)
    (parsed : { elf : File.ParsedElf //
                Parse.Segment.WellFormed (Parse.Segment.fromPhdrs elf.phdrs) })
    (h : 0 < objs.size) :
    0 < (integrate objs rest sn path handle parsed).fst.size := by
  by_cases hh : alreadyLoaded objs (canonicalName sn parsed.val) <;>
    simp [integrate, hh, Array.size_push, h]

end LeanLoad.Discover

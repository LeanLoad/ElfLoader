/-
Discover executor — IO instantiation.

The DFS traversal/finalization path lives in `Discover.DFS` and
`Discover.Build` — pure and generic over the effect monad. The
abstract IO leaf (`DependencyFinder m`) is in the public `LeanLoad.Discover`
interface. This file:

  · Builds `DependencyFinder.io` — production `find` composed from
    `Runtime.openByName` (C-side path search + open) + checked `Parse`.
    Canonical dedup key = `DT_SONAME` (production
    *requires* it; missing-SONAME deps fail loud).
  · Provides `discover` — the production entry. Opens the main
    executable via `Runtime.openByName` (literal-path case in the
    C function), parses it, names it via `LoadedObject.ofMain`
    (basename of `mainPath` — executables don't conventionally set
    SONAME), and drives the DFS via `discoverWith`.

Examples substitute a private in-memory `DependencyFinder` value for `DependencyFinder.io`
and call the same `discoverWith` — no IO needed.

Search rules (gabi 08 § Shared Object Dependencies) all live in
`Runtime.c` (`leanload_open_by_name`):
  1. If the name contains `/`, treat as a path directly.
  2. Else search `LD_LIBRARY_PATH`.
  3. Else search owning object's `DT_RUNPATH`.
`DT_RPATH` is deprecated and intentionally not honoured.
-/

import LeanLoad.Discover.Build
import LeanLoad.Parse
import LeanLoad.Runtime


namespace LeanLoad.Discover

open LeanLoad


-- ============================================================================
-- Checked parse over an already-open file. Used by both
-- `DependencyFinder.io.find` (DFS-discovered deps) and `discover` (main).
-- ============================================================================

/-- Parse and validate the open file. The file stays open for the loader's
    lifetime — used downstream by Exec for file-backed `mmap`.

    `Parse.parse` still separates byte I/O from pure validation
    internally; callers receive only the checked `Parse.Elf`. -/
def parseFromFile (file : Runtime.File) : IO Parse.Elf :=
  Parse.parse file

-- ============================================================================
-- DependencyFinder instance for production IO.
-- ============================================================================

/-- Production `DependencyFinder.find`: C-side search + open, then Lean-
    side checked parse. Canonical dedup key = `DT_SONAME` —
    required for every NEEDED-loaded `.so`. Fails loud if unset.

    Why required: SONAME is what makes cross-NEEDED dedup work
    (objects A and B both NEEDED the same library, possibly via
    different strings — same SONAME = dedup hits). Every modern
    toolchain sets it via `-Wl,-soname,…`; a SONAME-less `.so` is
    almost always a build mistake. Failing loud here is more
    diagnostic-friendly than silently double-loading. -/
def DependencyFinder.io : DependencyFinder IO :=
  { find := fun work => do
      match ← Runtime.openByName work.needed work.runpath with
      | none => pure none
      | some file => do
        let elf ← parseFromFile file
        match elf.soname with
        | some name => pure (some { name, handle := file, elf })
        | none      => throw (IO.userError
            s!"discover: '{work.needed}' is missing DT_SONAME (cannot dedup)")
    fail := fun {_} msg => throw (IO.userError msg) }

-- ============================================================================
-- discover — production entry point.
-- ============================================================================

/-- Walk `DT_NEEDED` from `mainPath` transitively. Returns a
    `LoadGraph` containing main and all reachable dependencies in
    DFS pre-order — non-emptiness, name-`Nodup`, `deps`-coherence,
    and `closure` (`deps[i].size = elf.needed.size`) all witnessed
    at the type level.

    Main is opened directly via `Runtime.openByName` (literal-path
    branch — `mainPath` contains '/'). Its canonical name is the
    path basename (via `LoadedObject.ofMain`); all NEEDED-loaded deps
    go through `DependencyFinder.io.find`, which *requires* DT_SONAME. -/
def discover (mainPath : String) : IO LoadGraph := do
  match ← Runtime.openByName mainPath none with
  | none => throw (IO.userError s!"discover: cannot open main '{mainPath}'")
  | some mainFile => do
    let mainElf ← parseFromFile mainFile
    discoverWith DependencyFinder.io 4096
      (LoadedObject.ofMain mainPath mainFile mainElf)

end LeanLoad.Discover

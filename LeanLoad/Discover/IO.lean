/-
Discover IO instantiation.

The DFS traversal/finalization path lives in `Discover.Traversal` and
`Discover.Finalize` — pure and generic over the effect monad. The abstract
object-discovery leaf (`ObjectFinder m`) is in the public `LeanLoad.Discover`
interface. This file:

  · Builds `ObjectFinder.io` — production `findMain` / `findDependency`
    composed from `Runtime.FileOps.io` (C-side path search + open/read) +
    checked `Parse.parseM`.
    Canonical dedup key = `DT_SONAME` (production
    *requires* it; missing-SONAME deps fail loud).
  · Provides the production `ObjectFinder.io` instantiation. `findMain`
    opens the main executable via `Runtime.FileOps.io` (literal-path case
    in the C function), parses it, and names it via `LoadedObject.ofMain`
    (basename of `mainPath` — executables don't conventionally set SONAME).

Examples substitute a private in-memory `ObjectFinder` value for `ObjectFinder.io`
and call the same monadic `discover` — no IO needed.

Search rules (gabi 08 § Shared Object Dependencies) all live in
`Runtime.c` (`leanload_open_by_name`):
  1. If the name contains `/`, treat as a path directly.
  2. Else search `LD_LIBRARY_PATH`.
  3. Else search owning object's `DT_RUNPATH`.
`DT_RPATH` is deprecated and intentionally not honoured.
-/

import LeanLoad.Discover.Finalize
import LeanLoad.Parse
import LeanLoad.Runtime.FileOps


namespace LeanLoad.Discover

open LeanLoad

private def parseFile (file : Runtime.File) : IO Parse.Elf := do
  match ← (Parse.parseM Runtime.FileOps.io file).run with
  | .ok elf  => pure elf
  | .error e => throw (IO.userError e)

/-- Production object finder: C-side search + open, then Lean-side checked parse.
    Main is named by path basename; dependency canonical dedup key is
    `DT_SONAME`, required for every NEEDED-loaded `.so`. Fails loud if unset.

    Why required: SONAME is what makes cross-NEEDED dedup work
    (objects A and B both NEEDED the same library, possibly via
    different strings — same SONAME = dedup hits). Every modern
    toolchain sets it via `-Wl,-soname,…`; a SONAME-less `.so` is
    almost always a build mistake. Failing loud here is more
    diagnostic-friendly than silently double-loading. -/
def ObjectFinder.io : ObjectFinder IO :=
  { findMain := fun mainPath => do
      match ← Runtime.FileOps.io.openByName mainPath none with
      | none => throw (IO.userError s!"discover: cannot open main '{mainPath}'")
      | some mainFile => do
        let mainElf ← parseFile mainFile
        pure (LoadedObject.ofMain mainPath mainFile mainElf)
    findDependency := fun work => do
      match ← Runtime.FileOps.io.openByName work.needed work.runpath with
      | none => pure none
      | some file => do
        let elf ← parseFile file
        match elf.soname with
        | some name => pure (some { name, handle := file, elf })
        | none      => throw (IO.userError
            s!"discover: '{work.needed}' is missing DT_SONAME (cannot dedup)")
    fail := fun {_} msg => throw (IO.userError msg) }

end LeanLoad.Discover

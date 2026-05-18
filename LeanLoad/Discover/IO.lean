/-
Discover executor — IO instantiation.

The BFS state machine (`bfsStep1`, `discoverLoopWith`) and its
invariant carrier (`BfsState`) live in `Discover.Step` — pure and
generic over the effect monad. This file:

  · Builds `Effects.io` — production `resolveDep` composed from
    `Runtime.openByName` (C-side path search + open) + `Parse` +
    `Elaborate`. Canonical dedup key = `DT_SONAME` when set, else
    the requested NEEDED string (matches ld.so when SONAME is unset).
  · Provides `discover` — the production entry. Opens the main
    executable via `Runtime.openByName` (literal-path case in the
    C function), parses it, computes its canonical name in Lean
    (basename of mainPath when SONAME is unset — the conventional
    case for executables), and drives the BFS via `discoverLoopWith`.

Tests substitute `Effects.test` (over an in-memory store) for
`Effects.io` and call the same `discoverLoopWith` — no IO needed.

Search rules (gabi 08 § Shared Object Dependencies) all live in
`Runtime.c` (`leanload_open_by_name`):
  1. If the name contains `/`, treat as a path directly.
  2. Else search `LD_LIBRARY_PATH`.
  3. Else search owning object's `DT_RUNPATH`.
`DT_RPATH` is deprecated and intentionally not honoured.
-/

import LeanLoad.Discover.BFS
import LeanLoad.Parse.RawElf
import LeanLoad.Elaborate.Elf
import LeanLoad.Runtime


namespace LeanLoad.Discover

open LeanLoad


-- ============================================================================
-- Parse + elaborate over an already-open handle. Used by both
-- `Effects.io.resolveDep` (BFS-discovered deps) and `discover` (main).
-- ============================================================================

/-- Byte-decode the open file then validate via `elaborate`. The
    handle stays open for the loader's lifetime — used downstream by
    Materialize for file-backed `mmap`.

    `Parse` (I/O — pread the bytes) and `Elaborate` (pure — gabi-07
    PT_LOAD checks + per-rela segment containment) are separate so
    I/O failure (short read, missing section) is distinguishable from
    validation failure (well-formed bytes that violate the spec). -/
def parseFromHandle (handle : Runtime.FileHandle) : IO Elaborate.Elf := do
  let raw ← Parse.RawElf.parse handle
  IO.ofExcept (Elaborate.elaborate raw)

-- ============================================================================
-- Effects instance for production IO.
-- ============================================================================

/-- Production `Effects.resolveDep`: C-side search + open, then Lean-
    side parse + elaborate. Canonical dedup key = `DT_SONAME` when
    set, else the NEEDED string the caller requested.

    The input-soname fallback is the only sound choice without a
    resolved-path return from C: it dedups correctly when the same
    NEEDED string appears multiple times (the common case — diamond
    deps), and is the same key ld.so would use against a SONAME-less
    file. The (rare) edge case "two different NEEDED strings resolve
    to the same SONAME-less file" can result in double-load, but
    every modern .so sets SONAME, so this is theoretical. -/
def Effects.io : Effects IO :=
  { resolveDep := fun soname runpath => do
      match ← Runtime.openByName soname runpath with
      | none => pure none
      | some handle => do
        let elf ← parseFromHandle handle
        pure (some (elf.soname.getD soname, handle, elf))
    fail := fun {_} msg => throw (IO.userError msg) }

-- ============================================================================
-- discover — production entry point.
-- ============================================================================

/-- `(s.splitOn "/").getLast?` — basename of a path. Used only for
    the main entry, where SONAME is conventionally unset and the
    user-supplied path is the natural canonical name source. -/
private def basename (s : String) : String :=
  (s.splitOn "/").getLast?.getD s

/-- Walk `DT_NEEDED` from `mainPath` transitively. Returns an
    `LoadGraph` containing main and all reachable dependencies in
    BFS order — non-emptiness, name-`Nodup`, and `deps`-coherence
    witnessed at the type level.

    Main is opened directly via `Runtime.openByName` (literal-path
    branch — `mainPath` contains '/'). Its canonical name is
    `DT_SONAME` if set, else `basename mainPath` (the convention
    for executables). All NEEDED-loaded deps go through
    `Effects.io.resolveDep`. -/
def discover (mainPath : String) : IO LoadGraph := do
  match ← Runtime.openByName mainPath none with
  | none => throw (IO.userError s!"discover: cannot open main '{mainPath}'")
  | some mainHandle => do
    let mainElf ← parseFromHandle mainHandle
    let mainName := mainElf.soname.getD (basename mainPath)
    let mainObj : LoadedObject :=
      { name := mainName, handle := mainHandle, elf := mainElf }
    discoverLoopWith Effects.io 4096 (BfsState.initial mainObj)

end LeanLoad.Discover

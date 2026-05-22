/-
Discover's abstract IO leaf.

The BFS driver (`Driver.lean`) is generic over the effect monad `m`;
it only knows that it can ask for a NEEDED soname to be resolved into
an open `(canonical, handle, elf)` triple — and that it can surface a
fatal error. Both leaves are bundled here as `Effects m`.

Two instantiations live downstream:

  · `Effects.io` (`IO.lean`) — production. `resolveDep` composes
    `Runtime.openByName` + `parseFromFile`; `fail` is
    `throw (IO.userError …)`.
  · `Effects.test` (`Test.lean`) — pure. `resolveDep` reads from an
    in-memory `TestStore`; `fail` is `Except.error`.

Kept in its own file so the abstract seam stays visible — neither
consumer pulls in the driver's invariant machinery just to instantiate
the record.
-/

import LeanLoad.Parse.Elf.Entry
import LeanLoad.Runtime

namespace LeanLoad.Discover

open LeanLoad

/-- The single IO leaf the BFS driver calls, plus a `fail` for the
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
      (env + runpath), open the file, and parse it. Returns:
      · `none` — soname didn't resolve to an existing file (missing dep).
      · `some (name, file, elf)` — `name` is the canonical dedup key
        (`DT_SONAME`; production *requires* it), `file` is the open file
        (kept for downstream `mmap`), `elf` is the checked view.
      Parse failures (including missing SONAME in production)
      escape via the monad's error mechanism (IO exception in production;
      `throw` in `Except`-based tests). Splitting "not found" out as a
      `none` instead of using `fail` lets the driver produce the
      diagnostic with the full `WorkItem` context (runpath, soname)
      attached. -/
  resolveDep : String → Option String →
               m (Option (String × Runtime.File × LeanLoad.Parse.Elf))
  /-- Surface a fatal error. In `IO`, this is `throw (IO.userError …)`;
      in `Except String`, it's `throw`. Polymorphic in the return type
      because the caller is in continuation position. -/
  fail       : {α : Type} → String → m α

end LeanLoad.Discover

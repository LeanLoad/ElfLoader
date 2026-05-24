/-
Discover's abstract resolver leaf.

The DFS traversal/finalization path is generic over the effect monad `m`;
it only knows that it can ask for a `WorkItem` to be resolved into a
checked `ResolvedObject` — and that it can surface a fatal error. Both
leaves are bundled here as `Resolver m`.

The production instantiation lives downstream:

  · `Resolver.io` (`IO.lean`) — production. `resolve` composes
    `Runtime.openByName` + `parseFromFile`; `fail` is
    `throw (IO.userError …)`.

`Discover.Examples` builds a private pure instantiation over an in-memory
store for `#guard` scenarios.

Kept in its own file so the abstract seam stays visible — neither
consumer pulls in the driver's invariant machinery just to instantiate
the record.
-/

import LeanLoad.Discover.Work

namespace LeanLoad.Discover

open LeanLoad

/-- The single IO leaf the DFS traversal calls, plus a `fail` for the
    missing-dep error. Parameterised over the effect monad `m` so
    examples can swap in a pure `Except String` (or `ReaderT` store)
    instance.

    The search-path arguments (`LD_LIBRARY_PATH`) are *not* passed
    through here — the production `Resolver.io` reads them inside the
    C runtime (`Runtime.openByName`). Examples construct their own
    `Resolver` value that closes over whatever environment they want
    to simulate. -/
structure Resolver (m : Type → Type) where
  /-- Resolve a `DT_NEEDED` work item against the runtime's search rules
      (env + runpath), open the file, and parse it. Returns:
      · `none` — the work item didn't resolve to an existing file.
      · `some obj` — `obj.name` is the canonical dedup key (`DT_SONAME`;
        production *requires* it), `obj.handle` is the open file (kept
        for downstream `mmap`), `obj.elf` is the checked view.
      Parse failures (including missing SONAME in production)
      escape via the monad's error mechanism (IO exception in production;
      `throw` in `Except`-based tests). Splitting "not found" out as a
      `none` instead of using `fail` lets the driver produce the
      diagnostic with the full `WorkItem` context (runpath, needed)
      attached. -/
  resolve : WorkItem → m (Option ResolvedObject)
  /-- Surface a fatal error. In `IO`, this is `throw (IO.userError …)`;
      in `Except String`, it's `throw`. Polymorphic in the return type
      because the caller is in continuation position. -/
  fail       : {α : Type} → String → m α

end LeanLoad.Discover

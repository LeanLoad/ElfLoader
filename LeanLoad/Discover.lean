/-
Discover stage public interface.

Discover turns a path-loaded main object plus a monadic dependency provider
into a witnessed dependency graph plus derived init order:

  · `Basic` — `LoadedObject` and explicit dependency `WorkItem`s.
  · `Names` — canonical naming policy for the main executable.
  · `Provider` — the object-finder seam used by CLI and examples.
  · `Graph` / `Order` — graph shape, init schedule, and order predicates.
  · `Builder` / `Traversal` / `Finalize` — construction state, DFS, and
    final promotion to `Result`.

This root module is intentionally a re-export facade; stage-specific code
imports the smallest Discover submodule it needs.
-/

import LeanLoad.Discover.Finalize

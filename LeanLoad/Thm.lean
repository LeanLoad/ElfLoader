/-
`LeanLoad.Thm` — typed index of all theorems in the project.

Reader's entry point at the type level. To audit the theorems
LeanLoad has proved, `import LeanLoad.Thm` and inspect this module
in the editor: every proven property is reachable from here, with
its full statement visible in tooltips.

For prose context (obligations O1–O6, what's proved vs. what's
deferred), see `docs/verification.md`.

Convention:

- Each theorem **statement** is the audit surface; proofs are black
  boxes (Lean's kernel checks them).
- Theorems live next to the definitions they're about, in the
  implementation file.
- This module re-exports them so a single import gives access to
  the full theorem catalogue.
- When proofs for a single topic grow past one screen, split that
  topic out into `LeanLoad/Thm/<Topic>.lean`. The import here stays
  unchanged.
-/

import LeanLoad.Link.Reloc.Aarch64
-- Future:
-- import LeanLoad.Thm.Layout    -- when O2 (disjointness) lands
-- import LeanLoad.Thm.Resolve   -- when O3 / resolution properties land

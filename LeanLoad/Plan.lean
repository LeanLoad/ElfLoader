/-
`LeanLoad.Plan` — pure planning over parsed ELF inputs.

Phase 2 includes only `Layout`. Phases 3-4 add `Resolve`, `Search`,
`Reloc`, `Init`.
-/

import LeanLoad.Plan.Layout
import LeanLoad.Plan.Resolve
import LeanLoad.Plan.Reloc
import LeanLoad.Plan.Reloc.Aarch64
import LeanLoad.Plan.Init

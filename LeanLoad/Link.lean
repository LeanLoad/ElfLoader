/-
`LeanLoad.Link` — pure planning over parsed ELF inputs.

Phase 2 includes only `Layout`. Phases 3-4 add `Resolve`, `Search`,
`Reloc`, `Init`.
-/

import LeanLoad.Link.Layout
import LeanLoad.Link.Search
import LeanLoad.Link.Resolve
import LeanLoad.Link.Reloc
import LeanLoad.Link.Reloc.Aarch64
import LeanLoad.Link.Init

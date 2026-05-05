# Plan

What's done, what's open, what's deliberately out of scope. For
architecture and the trust boundary, see `design.md`.

## Done

- **Parse.** Full loader-minimal parser (gabi 02–08). All `def`s
  total except `Parse.Dynamic.collect` (could be fueled).
- **Discover.** IO walk of `DT_NEEDED` with gabi 08 search-path
  rules. Builds a `LinkMap` in BFS order; libbar↔libbaz cycle
  handled via SONAME-keyed dedup.
- **Plan.** Pure pipeline: `Resolve` (BFS), `Layout` (one mapping per
  PT_LOAD), `Init` (DFS post-order, total via fuel), `Reloc` (planner
  parametric over per-arch `Formula`).
- **Load.** Maps memory, applies relocations, runs constructors,
  builds kernel-style stack, jumps. Static + dynamic both work
  end-to-end.
- **Theorems.** `vaToOffset_correct`, `fromLinkMap_layouts_size`,
  `fromLinkMap_deterministic`, `formula_is_total`,
  `formula_size_valid`. See `LeanLoad.Thm` and `verification.md`.

## Open

- **Differential testing against `ld.so`.** Run `leanload --inspect`
  vs `LD_DEBUG=files,reloc <bin>` on the same binary; diff. The
  strongest signal we can get without writing more theorems.
- **More relocation theorems.** Today we have totality + width
  validity for AArch64. Per-type correctness (`B+A` for RELATIVE,
  `S+A` for ABS64/GLOB_DAT/JUMP_SLOT) is currently `#guard` canaries
  next to the formula def; promote to theorems if the audit needs
  them.
- **`Parse.Dynamic.collect` totality.** Same fuel pattern as
  `Plan.Init.dfs` would do it.
- **Layout disjointness theorem (O2).** Needs an invariant on
  parsed `PT_LOAD`s (gabi 07 implies but doesn't state non-overlap).

## Out of scope

These are real concerns we deliberately defer. Each could land as
its own follow-up.

- **TLS** (`PT_TLS`, `R_AARCH64_TLS_*`). Its own subsystem (TLS
  template, per-thread blocks). The static and dynamic non-TLS
  cases work without it.
- **Lazy binding via PLT.** Bind everything at load time (eager).
  No `_dl_runtime_resolve` trampoline.
- **RELR-format relocations** (`.relr.dyn`). Requires a separate
  parser; currently disabled by *not* passing
  `-z pack-relative-relocs` to the linker.
- **`IFUNC` / `STT_GNU_IFUNC`.** GNU extension, glibc-only; musl
  doesn't emit these, so they don't appear in our fixtures.
- **`dlopen` / `dlsym`.** A loader-as-library API is a separate
  surface from "load and run".
- **Architectures other than AArch64.** The reloc planner is
  parametric over `Formula`, so adding a machine is one new file
  under `Spec/Reloc/` plus the `formulaFor` dispatch.
- **TLSDESC, GNU hash (`DT_GNU_HASH`-only), `.gnu.version_*`.**
  Modern GNU extensions. Match musl's defaults; revisit only if a
  fixture demands them.
- **Modeling `mmap`/`mprotect` semantics.** Trusted by inspection
  today; an abstract memory model + refinement proof is real
  research-level work and out of scope for v1.

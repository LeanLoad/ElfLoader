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
  `fromLinkMap_deterministic`, `Aarch64.formula_is_total` /
  `_size_valid`, `X86_64.formula_is_total` / `_size_valid`.
  See `LeanLoad.Thm` and `verification.md`.
- **Architectures.** AArch64 and x86-64. Per-arch reloc tables in
  `Spec/Reloc/{Aarch64,X86_64}.lean`; dispatch in `Plan/Formula.lean`.

## Open

- **`Parse.Dynamic.collect` totality.** Same fuel pattern as
  `Plan.Init.dfs` would do it.

### Theorem candidates (next to add)

Ordered by ROI, easiest first.

**Easy structural lemmas (`rfl`-class):**

- `Resolve.buildTable_deterministic` — `buildTable lm = buildTable lm`.
- `Plan.Reloc.plan_deterministic` — same args ⇒ same write array.
- `Plan.Init.finiOrder_eq_initOrder_reverse` — by definition.

**Structural invariants (one hour each):**

- `Plan.Init.initOrder_in_bounds` — every entry `i` of `initOrder lm`
  satisfies `i < lm.objects.size`. Requires exposing `dfs` and a
  fuel-induction lemma.
- `Plan.Init.initOrder_no_duplicates` — same indices never appear
  twice. Captures the cycle-breaking-via-visited invariant.
- `Plan.Layout.layouts_objectIdx_eq` — `layouts[i].objectIdx = i`.

**Per-type relocation correctness (one per row):**

Per-type `S + A` / `B + A` checks are currently `#guard` canaries
next to each `formula` def. Promote each to a theorem if the audit
demands them — straightforward unfolding proofs.

**Bigger pieces:**

- **`Plan.Reloc.plan_size_subset`** — given a hypothesis that the
  formula's output sizes satisfy some predicate `P`, every write the
  planner emits has `P size`. Then instantiate per arch with
  `P := (· = 4 ∨ · = 8)` to give a single bridge to `Load.Apply`'s
  width panic. Requires either refactoring `process` to use
  `Array.filterMap` or working through `Id.forIn` lemmas.
- **`Resolve.resolveByName_provider_defines`** — if it returns
  `(i, j)`, then `obj[i].symtab[j]` is a global def with name `name`.
  This is the gabi 08 contract. Same shape as `vaToOffset_correct`
  but needs a `findIdx?` analogue of `Array.exists_of_findSome?_eq_some`.
- **`Resolve.resolveByName_is_bfs`** — and no earlier index defines
  the same name. Captures gabi 08's "first match in BFS order".

**Out-of-reach without more infrastructure:**

- **Layout disjointness (O2).** `fromLinkMap` produces non-overlapping
  ranges. Needs an invariant on parsed `PT_LOAD`s (gabi 07 implies but
  doesn't state non-overlap).
- **Bytes preserved.** The materialised image at `va` equals the
  source byte at the corresponding file offset. Requires modelling
  the loaded image abstractly — the linksem-style soundness theorem,
  natural endpoint for the verified core.
- **Init topological order.** Every `DT_NEEDED` edge is respected:
  dependents run after their dependencies. Requires modelling the
  NEEDED graph; "undefined" for cycles per gabi 08.
- **`Discover.dedup`** as a theorem. Currently `partial def`;
  refactor to fuel-bounded recursion before proving.

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
- **Architectures other than AArch64 and x86-64.** The reloc planner
  is parametric over `Formula`, so adding a machine is one new file
  under `Spec/Reloc/` plus the `formulaFor` dispatch.
- **TLSDESC, GNU hash (`DT_GNU_HASH`-only), `.gnu.version_*`.**
  Modern GNU extensions. Match musl's defaults; revisit only if a
  fixture demands them.
- **Modeling `mmap`/`mprotect` semantics.** Trusted by inspection
  today; an abstract memory model + refinement proof is real
  research-level work and out of scope for v1.

# Plan

What's done, what's open, what's deliberately out of scope. For
architecture and the trust boundary, see `design.md`.

## Done

Pipeline (matches `--debug` output):

- **Parse** — full loader-minimal decoder (gabi 02–08; `DT_HASH` and
  `DT_GNU_HASH` for symtab sizing). All `def`s total except
  `Parse.Dynamic.collect` (could be fueled).
- **Discover** — IO walk of `DT_NEEDED` with gabi 08 search-path
  rules. Builds a `LinkMap` in BFS order; libbar↔libbaz cycle
  handled via SONAME-keyed dedup. Calls `Parse` per file.
- **Resolve** — pure BFS over `LinkMap` (gabi 08 § Shared Object
  Dependencies); outputs `(resolved, missing, weakMissing)`.
- **Layout** — `Layout.fromLinkMap` builds the per-object
  mappings (one `Mapping` per `PT_LOAD`) and the init/fini DFS
  post-order (total via fuel) in a single `Layout.Layout`
  bundle.
- **Map** — `mmap` per object (`MAP_FIXED` for `ET_EXEC`, anonymous +
  kernel-chosen base for `ET_DYN`), memcpy segment bytes, `mprotect`.
- **Reloc / Apply** — `Reloc.plan` evaluates per-arch `Formula`
  (AArch64 + x86-64); `Apply.applyAllRelocs` pokes the resulting bytes.
- **Init** — invoke each object's `DT_INIT_ARRAY` entries in
  `initOrder`.
- **Exec** — kernel-style stack (argc/argv/envp/auxv) + AArch64 /
  x86-64 trampolines; loaded program owns the process.

Static + dynamic both work end-to-end on AArch64 and x86-64.

- **Theorems.** `vaToOffset_correct`, `fromLinkMap_layouts_size`,
  `fromLinkMap_deterministic`, `Aarch64.formula_is_total` /
  `_size_valid`, `X86_64.formula_is_total` / `_size_valid`,
  `GnuHash.symCount_empty_buckets`, `GnuHash.findEndMarker_ge`,
  `GnuHash.symCount_gt_maxBucket`. See `LeanLoad.Thm` and
  `verification.md`.

## Open

- **`Parse.Dynamic.collect` totality.** Same fuel pattern as
  `Layout.dfs` would do it.

### Theorem candidates (next to add)

Ordered by ROI, easiest first.

**Easy structural lemmas (`rfl`-class):**

- `Resolve.buildTable_deterministic` — `buildTable lm = buildTable lm`.
- `Reloc.plan_deterministic` — same args ⇒ same write array.
- `Layout.finiOrder_eq_initOrder_reverse` — by definition.

**Structural invariants (one hour each):**

- `Layout.initOrder_in_bounds` — every entry `i` of `initOrder lm`
  satisfies `i < lm.objects.size`. Requires exposing `dfs` and a
  fuel-induction lemma.
- `Layout.initOrder_no_duplicates` — same indices never appear
  twice. Captures the cycle-breaking-via-visited invariant.
- `Layout.layouts_objectIdx_eq` — `layouts[i].objectIdx = i`.

**Per-type relocation correctness (one per row):**

Per-type `S + A` / `B + A` checks are currently `#guard` canaries
next to each `formula` def. Promote each to a theorem if the audit
demands them — straightforward unfolding proofs.

**Bigger pieces:**

- **`Reloc.plan_size_subset`** — given a hypothesis that the
  formula's output sizes satisfy some predicate `P`, every write the
  planner emits has `P size`. Then instantiate per arch with
  `P := (· = 4 ∨ · = 8)` to give a single bridge to `Apply`'s
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

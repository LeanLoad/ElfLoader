# Plan

Open work and what's deliberately out of scope. For architecture,
the pipeline, and the trust boundary, see `design.md`. The
proven-theorem catalogue lives under `LeanLoad/Thm/`.

## Open

### Theorem candidates (next to add)

**Structural invariants:**

- `Layout.initOrder_in_bounds` — every entry `i` of `initOrder lm`
  satisfies `i < lm.objects.size`. Requires exposing `dfs` and a
  fuel-induction lemma.
- `Layout.initOrder_no_duplicates` — same indices never appear
  twice. Captures the cycle-breaking-via-visited invariant.

**Bigger pieces:**

- **`Resolve.resolveByName_provider_defines`** — if it returns
  `(i, j)`, then `obj[i].symtab[j]` is a global def with name `name`.
  This is the gabi 08 contract. Same shape as `vaToOffset_correct`
  but needs a `findIdx?` analogue of `Array.exists_of_findSome?_eq_some`.
- **`Resolve.resolveByName_is_bfs`** — and no earlier index defines
  the same name. Captures gabi 08's "first match in BFS order".
- **`Resolve.buildTable_objectIdx_lt_size`** — every entry's
  `objectIdx < lm.objects.size`. Requires loop-invariant reasoning
  over `for ... in lm.objects do` (`Id.forIn` desugaring). Same shape
  as the `resolveByName` companion bound.

**Out-of-reach without more infrastructure:**

- **`segmentsSorted` from PT_LOAD invariant.** To actually invoke
  `segmentsPairwiseDisjoint_of_segmentsSorted` on a real ELF, we need
  to discharge `segmentsSorted` from a sortedness/non-overlap
  invariant on parsed `PT_LOAD`s (gabi 07 implies but doesn't formally
  state non-overlap).
- **Bytes preserved.** The materialised image at `va` equals the
  source byte at the corresponding file offset. Requires modelling
  the loaded image abstractly — the linksem-style soundness theorem,
  natural endpoint for the verified core.
- **BSS zeroed.** After `Map.mapObject`, every byte of every segment's
  `[p_vaddr + p_filesz, p_vaddr + p_memsz)` range reads as `0`.
  Currently provided informally by `mmap_anon` (kernel zero-fills) +
  explicit memset for the partial-last-page after a file-backed
  overlay. Proving it requires modelling `mmap_anon` + `memset`
  semantics — pairs with the abstract-memory-model work below.
- **Init topological order.** Every `DT_NEEDED` edge is respected:
  dependents run after their dependencies. Requires modelling the
  NEEDED graph; "undefined" for cycles per gabi 08.
- **Anonymous-mmap semantic model.** A pure `Memory` type with
  `[vaddr, vaddr+len)` ranges + per-byte content, plus a state-monad
  shadow for the IO operations (`mmapAnonFixed`, `mmapAt`, `write`,
  `mprotect`). Once present, "BSS zeroed" and "Bytes preserved"
  become provable as state-machine invariants. This is the linksem /
  CertiKOS tier of work — out of scope for v1.

### Reusable lemmas

When the proof set grows enough to need a `Lemmas/` directory, the
candidates we keep brushing against:

- `Array.findSome?` injectivity in single-cover settings.
- `ByteArray.extract` / index / size relations.
- `Parser` monad: cursor-monotonicity, leftover bytes, no panic.
- Page-alignment arithmetic.

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

# Verification

What LeanLoad proves, what it trusts, and where each lives.

The architecture isolates verifiable code (`Spec/`, `Parse/`, `Plan/`)
from trusted IO (`Discover.discover` body, `Load/`, `runtime/`); the
`LoaderPlan` is the refinement boundary.

## Where things live

- `LeanLoad/Spec/` — gabi/abi transcriptions only. Every type, constant,
  and table cites a specific spec section. The def *is* the spec.
- `LeanLoad/Parse/` — byte decoders.
- `LeanLoad/Plan/` — pure pipeline functions implementing gabi's
  prose-level algorithms (resolve, layout, init order, reloc planner).
- `LeanLoad/Discover.lean` — IO file walk + `LinkMap`.
- `LeanLoad/Map.lean` + `LeanLoad/Run.lean` — IO orchestration over `LoaderPlan`.
- `LeanLoad/Spec.lean` — catalogue/index of the spec surface.
- `LeanLoad/Thm.lean` — single audit surface for every proven property.

A reader auditing correctness reads `Spec.lean`, `Thm.lean`, plus the
cited gabi/abi sections.

## Reader's index of interfaces

| Type                    | Module             | Contract                                                |
| ----------------------- | ------------------ | ------------------------------------------------------- |
| `Parser α`              | `Parse.Bytes`      | Stateful read; advances the cursor or returns `Except`. |
| `ParsedElf`             | `Parse.File`       | Result of decoding one ELF byte sequence.               |
| `LinkMap`               | `Discover`         | Transitively-discovered dependency graph (BFS).         |
| `Plan.Resolve.SymRef`   | `Plan.Resolve`     | A resolved symbol: `(objectIdx, symIdx)`.               |
| `LoaderPlan`            | `Plan.Layout`      | Layouts + init/fini orders. **Refinement boundary.**    |
| `Plan.Reloc.Formula`    | `Plan.Reloc`       | `(type, S, A, B, P) → Option write`. Pluggable per-arch.|
| `Plan.Reloc.RelocWrite` | `Plan.Reloc`       | One planned memory write.                               |
| `FFI.Region.Region`     | `FFI.Region`       | Opaque mmap'd handle.                                   |

## Proved theorems

See `LeanLoad.Thm` for the canonical list. As of writing:

- `Parse.File.vaToOffset_correct` — VA → file-offset soundness (O3).
- `Plan.Layout.fromLinkMap_layouts_size` — one layout per object (O4).
- `Plan.Layout.fromLinkMap_deterministic` — same input, same output (O4).
- `Spec.Reloc.Aarch64.formula_is_total` — formula table is total.
- `Spec.Reloc.Aarch64.formula_size_valid` — every result has size ∈ {4,8};
  bridges the planner to `Load.Apply` (which panics on other widths).

## Project organization policy

1. **Module docstring as a spec contract.** Each `LeanLoad.Spec.*` /
   `LeanLoad.Parse.*` / `LeanLoad.Plan.*` module opens with the gabi /
   abi section it implements.
2. **All theorems live in `LeanLoad/Thm.lean`** — single audit surface.
   Proofs are short (1–5 lines); colocation with defs would buy refactor
   locality but lose the consolidated view.
3. **One file per spec concept.** `Spec/Header.lean` ↔ gabi 02,
   `Spec/Program.lean` ↔ gabi 07, etc.
4. **`Spec/` contains only what traces to official docs.** Project-defined
   types (`LinkMap`, `LoaderPlan`, `RelocWrite`) and pure pipeline
   functions live in `Plan/` or `Discover.lean`. Parsers live in `Parse/`.

Inspired by Kell, Mulligan, Sewell, *The Missing Link: Explaining ELF
Static Linking, Semantically* (OOPSLA 2016) — same definitions serve
execution and proof, with a single concrete correctness theorem for
one relocation type as the foothold.

## Proof obligations

### O1. Totality

Every `def` in `Spec/`, `Parse/`, and `Plan/` is total — Lean's
elaborator certifies it at type-check time. `Plan.Init.dfs` uses
fuel-based recursion (caller passes `lm.objects.size`, recursion
decrements). Remaining `partial def`s: `Discover.discover` (IO; the
filesystem and BFS dedup are the well-foundedness argument) and
`Parse.Dynamic.collect` (could be fueled the same way as `dfs`).

**Status: largely done** — only the two `partial def`s above remain.

### O3. `VA → file-offset` correctness within `PT_LOAD`

`Parse.File.vaToOffset phdrs va = some off` implies `off` is the file
position of the byte that should appear at virtual address `va`.

**Status: proved** (`vaToOffset_correct`). Soundness only; the
converse follows from `Array.findSome?`'s "first match" semantics
and is left as future work.

### O4. Plan determinism + structural integrity

`Plan.Layout.fromLinkMap` is pure (same input → same output) and
produces exactly one layout per discovered object — no drops, no
duplicates.

**Status: proved** (`fromLinkMap_deterministic`, `fromLinkMap_layouts_size`).

### O6. Relocation correctness (per-arch)

For each supported relocation type, the planned write matches the
formula in the per-arch ABI supplement.

**Status: AArch64 covered.** `formula_is_total` proves the table is
defined on every input. `formula_size_valid` proves every result has
size ∈ {4,8} — the bridge to `Load.Apply` which panics on other
widths. Per-type spot checks live as `#guard` canaries next to the
`formula` def in `Spec/Reloc/Aarch64.lean` (one per row of the gabi
table). x86-64 awaits an `EM_X86_64` formula table.

## Not currently in scope

- **Layout disjointness** — that `Plan.Layout.fromLinkMap` produces
  non-overlapping ranges. Needs an invariant on parsed `PT_LOAD`s
  (gabi 07 implies but doesn't state non-overlap). Future work.
- **Bytes preserved** — that the materialised image at `va` equals the
  source ELF byte at the corresponding file offset. Requires modelling
  the loaded image abstractly; aligns with the optional `mmap` model
  discussed below.
- **Equivalence to a specific `ld.so`.** Validated by differential
  testing (`plan.md` Phase 5), not by proof.
- **The kernel side of `mmap`/`mprotect`.** Trusted.
- **C shims under `runtime/`.** Audited by inspection (~150 lines).
- **`Discover.discover` IO body and `Load/`.** Sequence the verified
  core's outputs into IO actions; no novel logic.

## Trust assumptions on the host process

LeanLoad performs in-process loading: the loaded binary's segments
are `mmap`'d into leanload's own address space, and `Exec.run`
transfers control without first replacing the process image.
Verification of `Load` is conditioned on:

1. **Address-space disjointness.** The virtual-address ranges named
   by the `LoaderPlan` do not intersect any mapping currently in use
   by leanload itself.
2. **No concurrent address-space mutation.** No other thread calls
   `mmap` / `munmap` / `mprotect` / `mremap` during materialise→exec.
3. **No locks held across `Exec.run`.** No host thread holds a libc
   internal mutex (malloc arena, dynamic-loader lock, …) that the
   loaded binary will then try to acquire.
4. **Loaded binary uses `__NR_exit_group`, not `__NR_exit`.** The
   thread-scoped `exit` syscall would only kill the calling thread;
   other host threads survive and the process never terminates. The
   `examples/static.c` fixture honors this; musl's `_exit` does too.
5. **Signal handlers reset to `SIG_DFL`** before transfer of control,
   so the loaded binary's faults do not wake Lean's `segv_handler`
   (which deadlocks against libuv's pthread lock).

Phase 5 (differential testing) is the right time to revisit, either by
forking a single-threaded child before loading or by proving
fixture-specific instances of the assumptions.

## Reusable lemmas

The linksem paper notes: ~2500 of its 4500 proof lines were generic
lemmas about its data structures. We haven't accumulated enough to
need a `Lemmas/` directory yet; when we do, candidates are:

- `Array.findSome?` injectivity in single-cover settings.
- `ByteArray.extract` / index / size relations.
- `Parser` monad: cursor-monotonicity, leftover bytes, no panic.
- Page-alignment arithmetic.

# Verification

What we want to prove, in roughly increasing fidelity. The architecture
in `design.md` already isolates verifiable code (`Parse/`, `Link/`)
from trusted IO (`Discover`, `Load`, `runtime/`); the `LoaderPlan` is
the refinement boundary.

This file is the running plan for proofs. It evolves with the
implementation; theorems start as informal statements and become
machine-checked Lean theorems as they get proved.

## Project organization policy

**Goal:** a reader who wants to assess correctness should be able to
read this file plus the cited spec sections **and stop there**. They
should not have to read implementation code. The implementation may
be arbitrarily complex; what matters is a small set of **abstract
interfaces** with **stated contracts**.

The interfaces below are the audit surface. Each is a type plus
either an algebraic invariant or a theorem about it.

### Reader's index of interfaces

| Type                          | Module                | Contract                                                |
| ----------------------------- | --------------------- | ------------------------------------------------------- |
| `Parser α`                    | `Parse.Bytes`         | Stateful read; advances the cursor or returns `Except`. |
| `ParsedElf`                   | `Parse.File`          | Result of decoding one ELF byte sequence.               |
| `Closure`                     | `Discover`            | Transitively-discovered dependency graph.               |
| `Resolve.SymRef`              | `Link.Resolve`        | A resolved symbol: `(objectIdx, symIdx)`.               |
| `LoaderPlan`                  | `Link.Layout`         | Layouts + init/fini orders. **Refinement boundary.**    |
| `Reloc.Formula`               | `Link.Reloc`          | `(type, S, A, B, P) → Option write`. Pluggable per-arch.|
| `Reloc.RelocWrite`            | `Link.Reloc`          | One planned memory write.                               |
| `FFI.Region.Region`           | `FFI.Region`          | Opaque mmap'd handle. Finalizer calls `munmap`.         |
| `Load.Handle`                 | `Load`                | Owns regions for the lifetime of a load.                |

### Proved theorems

Each entry below is verbatim from the code; the reader may treat the
proof as a black box (Lean's kernel checks it).

- **AArch64 R_AARCH64_RELATIVE = B + A** (`Link.Reloc.Aarch64.formula_relative_correct`):

  ```lean
  theorem formula_relative_correct (inp : FormulaInputs) :
    formula R_AARCH64_RELATIVE inp =
      some { value := inp.base + inp.addend, size := 8 }
  ```

- **AArch64 R_AARCH64_GLOB_DAT = S + A** (`formula_glob_dat_correct`):

  ```lean
  theorem formula_glob_dat_correct (inp : FormulaInputs) :
    formula R_AARCH64_GLOB_DAT inp =
      some { value := inp.symValue + inp.addend, size := 8 }
  ```

- **AArch64 R_AARCH64_JUMP_SLOT = S + A** (`formula_jump_slot_correct`):

  ```lean
  theorem formula_jump_slot_correct (inp : FormulaInputs) :
    formula R_AARCH64_JUMP_SLOT inp =
      some { value := inp.symValue + inp.addend, size := 8 }
  ```

- **AArch64 R_AARCH64_ABS64 = S + A** (`formula_abs64_correct`):

  ```lean
  theorem formula_abs64_correct (inp : FormulaInputs) :
    formula R_AARCH64_ABS64 inp =
      some { value := inp.symValue + inp.addend, size := 8 }
  ```

- **R_AARCH64_NONE produces no write** (`formula_none_is_none`):

  ```lean
  theorem formula_none_is_none (inp : FormulaInputs) :
    formula R_AARCH64_NONE inp = none
  ```

- **`formula` is total** (`formula_is_total`): for every relocation
  type and every input, `formula` returns either `none` or a fully
  formed `FormulaResult`. No panic, no nontermination.

  ```lean
  theorem formula_is_total (ty : UInt32) (inp : FormulaInputs) :
    formula ty inp = none ∨ ∃ r, formula ty inp = some r
  ```

The reader who wants to confirm "AArch64 relocations are
specification-faithful" reads only this section. They never need to
open `LeanLoad/Link/Reloc/Aarch64.lean`.

Concretely:

1. **Module docstring as a spec contract.** Each `LeanLoad.Parse.*` /
   `LeanLoad.Link.*` module opens with (a) the gabi / x86-64-ABI
   section it implements (e.g. "gabi 06 § Relocation"), (b) the
   public API in one paragraph, (c) any obligations from this file
   (e.g. "addresses O3").
2. **Theorems live next to the definitions they're about.** Reader
   sees the function and its proven properties in one place. Move to
   `Thm/` only if proofs grow past a screen.
3. **One file per spec concept.** Already true: `Parse/Header.lean`
   ↔ gabi 02, `Parse/Program.lean` ↔ gabi 07, etc.
4. **No separate `Spec/` directory.** Cedar's split makes sense
   when an abstract semantics has multiple implementations. We have
   one implementation that **is** the spec (the relocation formula
   table is both); a separate `Spec/` would just duplicate code.
5. **Cite this file's obligation IDs (O1–O6) in theorem doc-comments**,
   so a reader of `Reloc/Aarch64.lean` knows where to find the
   broader story.

Closest reference projects we have in `third_party/` for this style:

- `lean4lean/` — transcribes a text-spec type theory into Lean,
  proves the kernel matches. Same shape as our "transcribe gabi".
- `cedar-spec/cedar-lean/Cedar/` — useful as a counterexample of
  when a `Spec/` + `Thm/` split *is* worth it (multiple impls of
  one semantics).

Inspired by Kell, Mulligan, Sewell, *The Missing Link: Explaining ELF
Static Linking, Semantically* (OOPSLA 2016) — see
`third_party/linksem/papers/oopsla-elf-linking-2016/`. Their approach:
same definitions serve execution and proof, with a single concrete
correctness theorem for one AMD64 relocation type as the foothold,
then expand. Lean 4 supports this natively without an extraction step.

## What the spec is

For each obligation, the spec is the cited gabi or x86-64-ABI section,
transcribed into a Lean proposition. We do **not** state new
specifications; we restate existing ones in machine-checked form.

## Proof obligations

### O1. Totality

Every `Parse.*` and `Link.*` definition terminates and returns
`Except String α` rather than panicking.

```
∀ (b : ByteArray), Parse.File.parse b terminates.
```

Status: most definitions are `def` (Lean infers termination); a few
are `partial def` (e.g. `Parse.Dynamic.collect`) and need work. The
linksem paper devoted ~1500 lines to termination; we can do better
with Lean's `decreasing_by` / fuel-based recursion.

### O2. Layout disjointness

Within one ELF, `Link.Layout.fromClosure` produces regions that do not
overlap in virtual address space.

```
∀ (elf : ParsedElf) (i j : Nat),
  i ≠ j →
  let regions := (Link.Layout.fromClosure elf).regions
  i < regions.size → j < regions.size →
  ¬overlap regions[i]! regions[j]!
where
  overlap r₁ r₂ : Bool :=
    (r₁.vaddr < r₂.vaddr + r₂.length) &&
    (r₂.vaddr < r₁.vaddr + r₁.length)
```

Status: not yet proved. Needs a precondition that the input ELF's
`PT_LOAD` segments themselves don't overlap (gabi 07 § Base Address
implies but doesn't state this); model that as a parser invariant.

### O3. `VA → file-offset` correctness within `PT_LOAD`

`Parse.File.vaToOffset phdrs va = some off` implies `off` is the file
position of the byte that should appear at virtual address `va`.

```
∀ phdrs va off,
  vaToOffset phdrs va = some off →
  ∃ ph ∈ phdrs,
    ph.p_type = PT_LOAD ∧
    ph.p_vaddr ≤ va ∧
    va < ph.p_vaddr + ph.p_memsz ∧
    off = ph.p_offset.toNat + (va - ph.p_vaddr).toNat
```

Status: provable by case analysis on `Array.findSome?`. Trivial.

### O4. Plan determinism

`Link.Layout.fromClosure` is a pure function; same input → same output.

```
∀ elf, Link.Layout.fromClosure elf = Link.Layout.fromClosure elf
```

Status: trivial (pure function). Worth stating to commit to determinism
as a design requirement (no maps with non-deterministic iteration, no
randomness, no timestamps).

### O5. Bytes preserved (Phase 2 specific)

For a static binary, the materialised image's bytes at virtual address
`va` equal the source ELF's bytes at the corresponding file offset, for
the file-backed portion of each `PT_LOAD`. The BSS tail is zero.

```
∀ elf bytes va,
  let plan := Link.Layout.fromClosure elf
  va ∈ fileBackedRange plan →
  loadedByte va = bytes[fileOffset va]!
```

Status: requires modelling the loaded image abstractly first. The
`Region` type in `Link.Layout` already has `fileOff`, `fileLen`,
`pageInset` — these are the operational ingredients.

### O6. Relocation correctness

For each supported relocation type, the planned write matches the
formula in `x86-64-ABI/object-files.tex` § Relocation Types.

```
-- For R_X86_64_64 = S + A:
∀ (r : RelaEntry),
  r.type = R_X86_64_64 →
  let plan := Link.Reloc.compute env r
  plan.targetAddr = r.r_offset + base ∧
  plan.value = symbolValue env r.sym + r.r_addend
```

Plan: prove `R_X86_64_64` first (as the linksem paper did for AMD64 —
their first theorem). Then `R_X86_64_RELATIVE`, `R_X86_64_GLOB_DAT`,
`R_X86_64_JUMP_SLOT`, `R_X86_64_PC32`. TLS relocations are out of
scope for v1 (see `plan.md`).

Status: not yet implemented. Phase 4.

## What we deliberately do **not** prove

- **Equivalence to a specific `ld.so`.** Validated by differential
  testing (per `plan.md` Phase 5), not by proof.
- **The kernel side of `mmap`/`mprotect` semantics.** Trusted.
- **C shims under `runtime/`.** Audited by inspection. The shims are
  thin (~150 lines total) and the surface is small enough that audit
  is feasible.
- **`Discover` and `Load`** (the IO orchestration). They contain no
  novel logic — they just sequence the verified core's outputs into
  IO actions.

## Trust assumptions on the host process

LeanLoad performs in-process loading: the loaded binary's segments
are `mmap`'d into leanload's own address space, and `Exec.run`
transfers control without first replacing the process image. Real
`execve(2)` resets the entire process; we do not. Verification of
`Load` is conditioned on the following assumptions about the host
process. Violations void the soundness of the runtime executor;
they do **not** affect proofs about `Parse` or `Link`.

1. **Address-space disjointness.** The virtual-address ranges named
   by the `LoaderPlan`'s regions (`p_vaddr` … `p_vaddr + p_memsz`,
   page-aligned) do not intersect any mapping currently in use by
   leanload itself — its `.text`/`.data`/`.bss`, heap, thread
   stacks, dynamically loaded libraries, or JIT mappings.
2. **No concurrent address-space mutation.** No other thread in the
   host process calls `mmap` / `munmap` / `mprotect` / `mremap`
   between the start of `Load.realize` and the call to `Exec.run`.
3. **No locks held across `Exec.run`.** No host thread holds a libc
   internal mutex (malloc arena, dynamic-loader lock, locale, etc.)
   that the loaded binary will then try to acquire.
4. **Loaded binary uses `__NR_exit_group`, not `__NR_exit`.** The
   thread-scoped `exit` syscall would only kill the thread that
   transferred control; other host threads survive and the process
   never terminates. Documented in `exec.md`; the `examples/static.c`
   fixture honors this.
5. **TLS / signals / `sigaltstack`** in the loaded program tolerate
   inheriting the host's state. (For static, no-libc fixtures this
   is trivial; for full glibc/musl programs it would not be.)

These assumptions are the multi-threading shadow over the entire
runtime side of LeanLoad. Phase 5 (differential testing) is the
right time to revisit, either by forking a single-threaded child
before loading or by proving fixture-specific instances of the
assumptions.

## Reusable lemmas

The linksem paper notes: ~2500 of its 4500 proof lines were generic
lemmas about its data structures, reusable across theorems. We expect
similar leverage. Likely candidates as we build them:

- `Array.findSome?` injectivity in single-cover settings.
- `ByteArray.extract` / index / size relations.
- `Parser` monad: cursor-monotonicity, leftover bytes, no panic.
- Page-alignment arithmetic (`alignDown`, `alignUp`, idempotence).

These will accumulate in their own modules under `LeanLoad/Lemmas/`
when the proof effort starts in earnest.

## Suggested order

1. Make every `Parse.*` and `Link.*` total (O1) — pre-requisite for
   everything else.
2. O3 (VA→offset) — small, useful, builds confidence.
3. O4 (determinism) — trivial; states the rule.
4. O2 (layout disjointness) — first non-trivial proof; needs an
   invariant on the parsed input.
5. O5 (bytes preserved) — Phase 2 capstone.
6. O6 (R_X86_64_64) — Phase 4 capstone; the linksem-equivalent
   theorem.

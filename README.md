# LeanLoad [![CI](https://github.com/ShawnZhong/LeanLoad/actions/workflows/ci.yml/badge.svg)](https://github.com/ShawnZhong/LeanLoad/actions/workflows/ci.yml)

A verified ELF loader in Lean 4. Reads, plans, and runs Linux ELF
binaries (static + dynamically-linked) through a pipeline split into
a **pure middle** (verified core, all in `Plan/`) and two **trusted
IO bookends**:

| Stage    | Pure planner    | IO bookend                | What it does                                                                                  |
| -------- | --------------- | ------------------------- | --------------------------------------------------------------------------------------------- |
| Discover | `Plan/Discover` | `Discover.discover`       | Walk `DT_NEEDED`, BFS-dedup; produce non-empty `ObjectList`.                                  |
| Parse    | `Parse/*`       | `Parse/File.parse`        | Decode each ELF; carry a `WellFormed` segment witness in the type.                            |
| Resolve  | `Plan/Resolve`  | —                         | Match each undef ref to a providing `(object, symbol)` via `Fin n`-typed `SymRef`.            |
| Layout   | `Plan/Layout`   | —                         | Pick per-object mmap base; carry sorted-segments witness in the type.                         |
| Reloc    | `Plan/Reloc`    | (folded into `realize`)   | Per-arch formula → `Patch` list; `PatchSize` (`b4`/`b8`) makes realize dispatch structural.   |
| Init     | `Plan/Init`     | (folded into `realize`)   | DFS post-order over deps, then per-object `init_array` resolution → constructor address list. |
| Exec     | —               | `Exec.realize`            | Single IO sweep over layouts/patches/ctors: mmap + zeroout + mprotect + patch writes + ctor calls + stack + jump. |

Every file under `Plan/` is pure Lean; the only IO seams are
`Discover` (file reads) and `Exec.realize` (mmap + writes +
control transfer). The mmap-op sequence (overlay/bssZero/mprotect)
is derived inline from each layout's segments inside `realize` —
there's no separate Map planner because that "planning" was
trivial (a function of segment shape) and only `realize` consumed it.

Targets AArch64 + x86-64 with musl libc. The verified core is pure
Lean.

https://github.com/ShawnZhong/LeanLoad/blob/8efc31143c07302e9fc5743b7e144602fd5eb0c2/run.log#L1-L213

## Quick start

```sh
./setup.sh               # one-shot: install system C toolchain, init submodules
./run.sh                 # build leanload + examples, run on build/main
./run.sh build/static    # run on the static fixture
./test.sh                # build examples + run the Lean test suite
```

## Documentation

- [`docs/design.md`](docs/design.md) — pipeline, trust boundary,
  naming conventions, CLI, kernel-style exec, host-process trust
  assumptions.
- [`docs/plan.md`](docs/plan.md) — open work and out-of-scope items.

The audit surface inside the code is `LeanLoad/Spec/` (gabi/abi
transcriptions, one file per chapter) and `LeanLoad/Thm/` (every
machine-checked theorem, one file per topic).

## Status

- Static binary (no libc): runs end-to-end via `leanload examples/build/static`.
- Dynamic binary (musl-linked, multi-shared-object closure): runs
  end-to-end against `examples/build/main`.
- Differential tests against `ld.so` are not yet wired up.

## Module layout

```
LeanLoad.lean              package root (re-exports)
LeanLoad/
  Spec/                    gabi/abi transcriptions — types and constants only, no logic
    Header.lean            gabi 02 § ELF Header (ElfHeader64, ELFMAG, ET_*, EM_*)
    Program.lean           gabi 07 § Program Header (PT_*, PF_*, Header64)
    Dynamic.lean           gabi 08 § Dynamic Section (DT_* tags, Dyn64)
    StringTable.lean       gabi 04 § String Table (NUL-terminated lookup by offset)
    Symbol.lean            gabi 05 § Symbol Table (STB_*, STT_*, Symbol64, bind/type extract)
    Reloc.lean             gabi 06 § Relocation (Rela64, sym/type extract from r_info)
    Reloc/Aarch64.lean     aarch64-elf-abi § Dynamic Relocations (per-type formula table)
    Reloc/X86_64.lean      x86-64-ABI § Relocation Types (per-type formula table)
    Reloc/Formula.lean     per-`e_machine` dispatch to the right per-arch formula
    GnuHash.lean           gnu-gabi § Hashes (layout + dynsym-count derivation)
  Parse/                   byte decoders — one file per Spec/ section
    Bytes.lean             parser monad (cursor + Except, u32le / u64le primitives)
    Header.lean            ElfHeader64 decoder
    Program.lean           Header64 decoder + table reader
    Dynamic.lean           .dynamic decoder + tag-keyed lookups (find?, findAll)
    StringTable.lean       view a `ByteArray` slice as a string table
    Symbol.lean            Symbol64 decoder
    Reloc.lean             Rela64 decoder
    Segment.lean           Segment + WellFormed (sorted, sized, aligned, congruent, non-overlap)
    GnuHash.lean           DT_GNU_HASH chain reader → dynsym count
    File.lean              ParsedElf aggregate + top-level parse with WellFormed witness
  Thm/                     proven theorems — one file per topic, docstring is the contract
    Parse.lean             named accessors deriving Spec.Program.{Sorted,…} from a WellFormed witness
    Layout.lean            sorted ⇒ pairwise disjoint; runtime check ↔ proof-level invariant
    Discover.lean          BFS dedup primitive iff loaded; nodup-preservation on push
    GnuHash.lean           soundness of the dynsym-count derivation
  Plan/                    pure middle — every stage that produces abstract data
    Discover.lean          BFS dedup + LoadedObject + ObjectList (non-empty subtype)
    Resolve.lean           undef ref → SymRef n / Unresolved n / Table n (Fin n on objectIdx)
    Layout.lean            per-object Segment + ObjectLayout; assignBases; layouts validator
    Reloc.lean             Patch n (Fin objectIdx) + PatchSize (b4/b8); planner per-arch formula
    Init.lean              buildDeps (HashMap O(N+E)) + DFS post-order + ctor address list
  Discover.lean            walk DT_NEEDED via IO; thread non-emptiness witness through the loop
  Exec.lean                IO bookend — realize all plans (mmap + zeroout + mprotect + patch
                           writes + ctor calls + stack + execAndJump). Does not return.
  Runtime.lean             @[extern] trust seam (FileHandle, Region, mmap*, patch{32,64}, …)
  Main.lean                CLI + load / debug orchestration
  Test.lean                test exe entry — drives every stage except Exec
  Fixtures.lean            shared synthObj for `#guard` blocks
runtime/                   C shims (unverified)
  runtime.h                shared header (decls + helpers)
  region.c                 mmap / mprotect / write
  exec.c                   ctor invocation + transfer of control
docs/                      design.md · plan.md
examples/                  C sources for showcase binaries
third_party/               submodules (musl, nolibc, gabi, …)
```

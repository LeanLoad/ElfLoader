# LeanLoad [![CI](https://github.com/ShawnZhong/LeanLoad/actions/workflows/ci.yml/badge.svg)](https://github.com/ShawnZhong/LeanLoad/actions/workflows/ci.yml)

A verified ELF loader in Lean 4. Reads, plans, and runs Linux ELF
binaries (static + dynamically-linked) through a pipeline split into
**pure planners** (verified core) and **trusted IO appliers** (FFI to
`mmap` / `mprotect` / `pread`):

| Stage    | Pure planner   | Trusted IO         | What it does                                                                                  |
| -------- | -------------- | ------------------ | --------------------------------------------------------------------------------------------- |
| Discover | `DiscoverPlan` | `DiscoverApply`    | Walk `DT_NEEDED`, BFS-dedup; produce non-empty `ObjectList`.                                  |
| Parse    | `Parse/*`      | `Parse/File.parse` | Decode each ELF; carry a `WellFormed` segment witness in the type.                            |
| Resolve  | `Resolve`      | —                  | Match each undef ref to a providing `(object, symbol)` via `Fin n`-typed `SymRef`.            |
| Layout   | `Layout`       | —                  | Pick per-object mmap base; carry sorted-segments witness in the type.                         |
| Map      | `MapPlan`      | `MapApply`         | Anon reservation + per-segment overlay/zero/mprotect; `Fin segIdx` for total slot writes.     |
| Reloc    | `RelocPlan`    | `RelocApply`       | Per-arch formula → `Patch` list; `PatchSize` (`b4`/`b8`) makes apply dispatch structural.     |
| Init     | `InitPlan`     | `InitApply`        | DFS post-order over deps, then per-object `init_array` resolution → constructor address list. |
| Exec     | —              | `Exec`             | Build kernel-style stack + auxv; jump to entry. Does not return.                              |

Every `*Plan` is pure Lean; every `*Apply` only orchestrates IO calls
the planner already approved.

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
    Parse.lean             VA → file-offset soundness within PT_LOAD; WellFormed ↔ WellFormedB
    Layout.lean            sorted ⇒ pairwise disjoint; runtime check ↔ proof-level invariant
    Resolve.lean           findInObject's index is in-bounds of obj.elf.symtab
    Discover.lean          BFS dedup primitive iff loaded; nodup-preservation on push
    GnuHash.lean           soundness of the dynsym-count derivation
  DiscoverPlan.lean        BFS dedup + LoadedObject + ObjectList (non-empty subtype)
  DiscoverApply.lean       walk DT_NEEDED via IO; thread non-emptiness witness through the loop
  Resolve.lean             undef ref → SymRef n / Unresolved n / Table n (Fin n on objectIdx)
  Layout.lean              per-object Segment + ObjectLayout; assignBases; layouts validator
  Image.lean               ProcessImage n (parameterised by object count, size_eq witness)
  MapPlan.lean             ObjectPlan + PerObjectOp numSegs (Fin segIdx)
  MapApply.lean            mmap + memcpy + mprotect (IO); per-object iteration
  RelocPlan.lean           Patch n (Fin objectIdx) + PatchSize (b4/b8); planner per-arch formula
  RelocApply.lean          dispatch on PatchSize; total `image.objects[p.objectIdx]` (Fin n)
  InitPlan.lean            buildDeps (HashMap O(N+E)) + DFS post-order + ctor address list
  InitApply.lean           call each constructor address (IO)
  Exec.lean                kernel-style stack + auxv + transferControl (does not return)
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

# LeanLoad [![CI](https://github.com/ShawnZhong/LeanLoad/actions/workflows/ci.yml/badge.svg)](https://github.com/ShawnZhong/LeanLoad/actions/workflows/ci.yml)

A verified ELF loader in Lean 4. Reads, plans, and runs Linux ELF
binaries (static + dynamically-linked) through a seven-stage pipeline:

- **Discover** — walk `DT_NEEDED`, parse each file, build the link map.
- **Resolve** — find each undef symbol's defining object via BFS.
- **Layout** — compute per-object mmap layout and init/fini order.
- **Map** — `mmap` each object's segments; kernel picks bases.
- **Reloc** — compute per-arch relocation writes.
- **Apply** — execute the writes into mmap'd memory.
- **Exec** — call constructors in init order, build a kernel-style stack, jump to entry.

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
    GnuHash.lean           DT_GNU_HASH chain reader → dynsym count
    File.lean              ParsedElf aggregate + top-level parse
  Thm/                     proven theorems — one file per topic, docstring is the contract
    Parse.lean             VA → file-offset soundness within PT_LOAD
    Layout.lean            layout determinism; segment containment; sorted ⇒ pairwise disjoint
    Reloc.lean             per-arch reloc widths are 4 or 8; planner→applier width bridge
    Resolve.lean           symbol indices returned by lookup are in-bounds
    Discover.lean          BFS dedup primitive matches its intended predicate
    GnuHash.lean           soundness of the dynsym-count derivation
  Main.lean                CLI + `load` orchestration
  Test.lean                test exe entry — drives every stage except Exec
  Fixtures.lean            shared synthObj/synthElf for `#guard` blocks
  Discover.lean            IO walk + LinkMap type
  Resolve.lean             undef ref → providing object/symbol (pure)
  Layout.lean              per-object Segment + ObjectLayout; disjointness predicates
  Order.lean               init/fini DFS post-order over DT_NEEDED (gabi 08)
  Reloc.lean               formula → write list (pure, post-bases)
  Map.lean                 mmap + memcpy + mprotect (IO)
  Apply.lean               poke reloc bytes into mmap'd memory (IO)
  Runtime.lean             @[extern] trust seam (runtime/*.c)
  Exec.lean                init/fini calls + control transfer (IO)
runtime/                   C shims (unverified)
  runtime.h                shared header (decls + helpers)
  region.c                 mmap / mprotect / write
  exec.c                   ctor invocation + transfer of control
docs/                      design.md · plan.md
examples/                  C sources for showcase binaries
third_party/               submodules (musl, nolibc, gabi, …)
```

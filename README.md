# LeanLoad [![CI](https://github.com/ShawnZhong/LeanLoad/actions/workflows/ci.yml/badge.svg)](https://github.com/ShawnZhong/LeanLoad/actions/workflows/ci.yml)

A verified ELF loader in Lean 4. Reads, plans, and runs Linux ELF
binaries (static + dynamically-linked) through an eight-stage pipeline:

- **Discover** — walk `DT_NEEDED`, parse each file, build the link map.
- **Resolve** — find each undef symbol's defining object via BFS.
- **Layout** — compute per-object mmap layout and init/fini order.
- **Map** — `mmap` each object's segments; kernel picks bases.
- **Reloc** — compute per-arch relocation writes.
- **Apply** — execute the writes into mmap'd memory.
- **Init** — call constructors in dependency order.
- **Exec** — build a kernel-style stack and jump to entry.

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
  naming conventions, CLI, kernel-style exec details.
- [`docs/verification.md`](docs/verification.md) — proof obligations,
  proven theorems, trust assumptions on the host process.
- [`docs/plan.md`](docs/plan.md) — phased implementation plan and
  current status.

The audit surface inside the code is `LeanLoad/Spec/` (gabi/abi
transcriptions, one file per chapter) and `LeanLoad/Thm.lean`
(every machine-checked theorem in one place).

## Status

- Static binary (no libc): runs end-to-end via `leanload examples/build/static`.
- Dynamic binary (musl-linked, multi-shared-object closure): runs
  end-to-end against `examples/build/main`.
- Differential tests against `ld.so` are not yet wired up.

## Module layout

```
LeanLoad.lean              package root (re-exports)
LeanLoad/
  Main.lean                CLI + `load` orchestration
  Test.lean                test exe entry
  Discover.lean            IO walk + LinkMap type
  Resolve.lean             undef ref → providing object/symbol (pure)
  Layout.lean              mappings + init/fini order (pure)
  Reloc.lean               formula → write list (pure post-bases)
  Map.lean                 mmap + memcpy + mprotect (IO)
  Apply.lean               poke reloc bytes into mmap'd memory (IO)
  Region.lean              @[extern] for memory ops (runtime/region.c)
  Exec.lean                @[extern] for control transfer + init/exec
  TestFixture.lean         shared synthObj/synthElf
  Thm.lean                 single audit surface for proven theorems
  Spec/                    gabi/abi transcriptions only
    Header.lean            gabi 02 § ELF Header
    Program.lean           gabi 07 § Program Header
    Dynamic.lean           gabi 08 § Dynamic Section
    StringTable.lean       gabi 04 § String Table
    Symbol.lean            gabi 05 § Symbol Table
    Reloc.lean             gabi 06 § Relocation
    Reloc/Aarch64.lean     aarch64-elf-abi § Dynamic Relocations
    Reloc/X86_64.lean      x86-64-ABI § Relocation Types
    Reloc/Formula.lean     per-`e_machine` dispatch (gabi 02 § e_machine)
    GnuHash.lean           gnu-gabi § Hashes
  Parse/                   byte decoders (impl)
    Bytes.lean             parser monad
    Header.lean Program.lean Dynamic.lean
    StringTable.lean Symbol.lean Reloc.lean
    File.lean              ParsedElf aggregate + parse
runtime/                   C shims (unverified)
  region.{h,c}             mmap / mprotect / write
  exec.{h,c}               ctor invocation + transfer of control
  common.h                 shared lean-FFI helpers
docs/                      design.md · plan.md · verification.md
examples/                  C sources for showcase binaries
third_party/               submodules (musl, nolibc, gabi, …)
```

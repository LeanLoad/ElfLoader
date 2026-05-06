# LeanLoad

A verified ELF loader in Lean 4. Reads, plans, and runs Linux ELF
binaries (static + dynamically-linked) through an eight-stage pipeline:

- **Discover** — walk `DT_NEEDED`, parse each file, build the link map.
- **Resolve** — find each undef symbol's defining object via BFS.
- **Plan** — compute per-object mmap layout and init/fini order.
- **Map** — `mmap` each object's segments; kernel picks bases.
- **Reloc** — compute per-arch relocation writes.
- **Apply** — execute the writes into mmap'd memory.
- **Init** — call constructors in dependency order.
- **Exec** — build a kernel-style stack and jump to entry.

Targets AArch64 + x86-64 with musl libc. The verified core is pure
Lean.

https://github.com/ShawnZhong/LeanLoad/blob/59fceebb199e9a367e1fee6d979909ca566efe20/run.log#L1-L213

## Quick start

```sh
./setup.sh               # one-shot: install system C toolchain, init submodules
./run.sh                 # build leanload + examples, run on build/main
./run.sh build/static    # run on the static fixture
./test.sh                # build examples + run the Lean test suite
```

## Documentation

- [`docs/design.md`](docs/design.md) — pipeline, module layout, trust
  boundary, naming conventions, CLI.
- [`docs/verification.md`](docs/verification.md) — proof obligations,
  proven theorems, trust assumptions on the host process.
- [`docs/exec.md`](docs/exec.md) — kernel-style stack (argc/argv/envp/auxv),
  signal-handler reset, AArch64 + x86-64 trampolines.
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

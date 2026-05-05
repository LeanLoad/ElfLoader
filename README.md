# LeanLoad

A verified ELF loader in Lean 4. Reads, plans, and runs Linux ELF
binaries (static + dynamically-linked) **without `execve`** — the
loader maps each object into the host process's address space,
applies relocations, calls constructors, builds a kernel-style stack,
and jumps. Targets AArch64 + musl libc.

The verified core is pure Lean. The syscall layer is a thin C shim
behind two `@[extern]` modules.

## Quick start

```sh
./setup.sh               # one-shot: install system C toolchain, init submodules
./run.sh                 # build leanload + examples, run on build/main
./run.sh build/static    # run on the static fixture
./test.sh                # build examples + run the Lean test suite
```

The Lean toolchain itself is auto-installed by `elan` from
`lean-toolchain`.

Direct CLI:

```sh
./.lake/build/bin/leanload <elf>             # load and run; does not return
./.lake/build/bin/leanload --inspect <elf>   # print the planned layout
```

## Documentation

- [`docs/design.md`](docs/design.md) — pipeline, module layout, trust
  boundary, naming conventions, CLI.
- [`docs/verification.md`](docs/verification.md) — proof obligations,
  proven theorems, trust assumptions on the host process.
- [`docs/exec.md`](docs/exec.md) — kernel-style stack (argc/argv/envp/auxv),
  signal-handler reset, AArch64 trampoline.
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

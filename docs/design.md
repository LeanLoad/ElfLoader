# LeanLoad Design

Verified ELF loader in Lean 4. The verified core is pure Lean; the
syscall layer sits behind FFI.

## Phases

1. **Parse** (pure, single file): bytes → typed ELF records — header
   (gabi 02), program headers (gabi 07), `.dynamic` array (gabi 08),
   dynsym/dynstr (gabi 04, 05), relocation tables (gabi 06).
2. **Discover** (`IO`): walk `DT_NEEDED` transitively (gabi 08, §
   Shared Object Dependencies). Resolve via `DT_RUNPATH` /
   `LD_LIBRARY_PATH` / default paths. Read each dependency with
   `IO.FS.readBinFile`, call `Parse` on its bytes. Returns a
   `LoaderInput` mapping path → parsed ELF.
3. **Link** (pure): operate on the full input set. Resolve symbols
   breadth-first (gabi 08, § Shared Object Dependencies); compute
   mmap layout from `PT_LOAD` (gabi 07); build relocation writes
   using x86-64 formulas (`x86-64-ABI/object-files.tex`, § Relocation
   Types). Output is a `LoaderPlan` — pure data, no `IO`.
4. **Load** (`IO`, FFI-backed): execute the plan. `mmap` segments
   per `p_vaddr`/`p_filesz`/`p_memsz` (gabi 07), copy bytes, apply
   relocations, `mprotect` per `PF_R`/`PF_W`/`PF_X` (gabi 07), run
   constructors via `DT_PREINIT_ARRAY`/`DT_INIT_ARRAY`/`DT_INIT`
   (gabi 08, § Initialization and Termination), transfer control to
   entry, run destructors on exit.

The plan is the refinement boundary. Proofs target `Parse` and `Link`.
`Discover` and `Load` are trusted IO code.

## Scope

**Architecture: x86-64 ELF64 only.** Committed. Concrete struct types
(`ElfHeader64`, `ProgramHeader64`, `Rela64`); no 32-bit / typeclass
abstraction layer. Other classes or machines are out of scope; revisit
only if a concrete need appears.

**Parser scope: loader-minimal.** A loader does not need to parse the
full ELF, only what is reachable from program headers and the dynamic
section.

- Parsed: ELF header; program header table; `PT_DYNAMIC` and the
  `.dynamic` array; dynsym + dynstr; `Rela`/`Rel` and `JMPREL`
  tables; `PT_INTERP`; `PT_TLS`; init/fini arrays.
- Skipped: section headers, `.text`/`.bss`/`.rodata` section
  metadata, debug info, hash tables (only needed for lazy
  resolution, which v1 does not implement).

Module split (each module's source spec in parens):

| Module             | Source spec                                        |
| ------------------ | -------------------------------------------------- |
| `Parse/Header`     | gabi 02 `02-eheader.rst`                           |
| `Parse/Program`    | gabi 07 `07-pheader.rst`                           |
| `Parse/Dynamic`    | gabi 08 `08-dynamic.rst` § Dynamic Section         |
| `Parse/Symbol`     | gabi 04 `04-strtab.rst`, 05 `05-symtab.rst`        |
| `Parse/Reloc`      | gabi 06 `06-reloc.rst`                             |
| `Parse/File`       | aggregate                                          |
| `Link/Resolve`     | gabi 08 § Shared Object Dependencies               |
| `Link/Search`      | gabi 08 § Shared Object Dependencies (`DT_RUNPATH`, `LD_LIBRARY_PATH`) |
| `Link/Layout`      | gabi 07 § Base Address, Segment Permissions        |
| `Link/Reloc`       | x86-64-ABI `object-files.tex` § Relocation Types   |
| `Link/Init`        | gabi 08 § Initialization and Termination Functions |

**Reference docs (in `third_party/`):**
- `gabi/docsrc/elf/{02-eheader,07-pheader,08-dynamic,...}.rst` for
  the architecture-neutral format.
- `x86-64-ABI/x86-64-ABI/{object-files,dl}.tex` for `R_X86_64_*`
  relocation formulas and PLT/GOT mechanics.
- `ELFSage/ELFSage/Types/` is a working Lean 4 ELF parser; useful
  as a reference for module organization, but parses more than a
  loader needs.

## Directory layout

```
LeanLoad.lean              package root
Main.lean                  CLI entry
LeanLoad/                  Lean modules
  Basic.lean
  Parse/                   ELF decoding (pure)
  Link/                    resolution, layout, relocation planning (pure)
  FFI/                     @[extern] declarations (trusted)
    Fd.lean
    Region.lean
    Exec.lean
  Load.lean                IO orchestration: Parse + Link + FFI
runtime/                   C shims (unverified)
  fd.h    fd.c             open / read / fstat / close
  region.h region.c        mmap / munmap / mprotect / accessors
  exec.h  exec.c           ctor / entry / dtor invocation
docs/
  bg-ffi.md                FFI background (general reference)
  design.md                this file
  plan.md                  phased implementation plan
examples/                  C sources + Makefile for showcase binaries
Tests/                     Lean tests (lake test entry: Tests/Test.lean)
third_party/               submodules
```

## Trust boundary

- **Verified**: `LeanLoad/Parse/` and `LeanLoad/Link/`. Pure Lean,
  no `IO`, no `LeanLoad.FFI` imports.
- **Trusted**: `LeanLoad/FFI/*` and `runtime/*`. Audited by inspection.
- **Glue**: `LeanLoad/Load.lean` — the only module allowed to import
  both verified and FFI namespaces.

A grep for `import LeanLoad.FFI` outside `Load.lean` is a smell.

## Naming conventions

- Lean module `LeanLoad.FFI.Region` ↔ C file `runtime/region.c`.
- Extern symbols prefixed `leanload_<topic>_<op>`:
  `leanload_region_mmap`, `leanload_fd_open`, etc. Flat C namespace,
  so the prefix avoids collisions and aids grep.
- Opaque Lean types named for what they are (`Fd`, `Region`), not how
  they are implemented — no `Ptr` suffix.

## Memory ownership

- **Inputs** (ELF files): read via `IO.FS.readBinFile` into a
  `ByteArray`. Small enough that the copy is free, and `Link` reasons
  over pure data.
- **Outputs** (loaded image): `mmap` regions wrapped as opaque
  `Region` external objects. Finalizer calls `munmap`. Writes happen
  during `Load`.

See `docs/bg-ffi.md` for the underlying FFI patterns.

## Build

`lakefile.lean` (not `.toml` — needs custom native targets). Builds
both a static archive (`libleanload_runtime.a`) and a shared library
(`libleanload_runtime.so`) for the `runtime/` sources. The static
archive is linked into AOT binaries; the shared library is loaded by
the Lean interpreter for `#eval` and editor sessions.

C, not C++. The shims are thin libc wrappers; there is no need for
RAII or templates, and `lean.h` compiles cleanly in C. This avoids
linking `libstdc++`. Switch to C++ later if a C++ dependency forces
the issue.

## CLI

Two invocations:

```
leanload <elf>             # run the binary
leanload --inspect <elf>   # run Parse + Discover + Link, dump the plan, exit
```

`--inspect` stops before `Load`. No `mmap`, no execution. The dump is
the union of `LoaderInput` (parsed deps) and `LoaderPlan` (mmap
layout, relocation writes, init/fini order).

No subcommands, no `--debug=` topics, no `--stop-at`. The pipeline is
short enough that a single dump covers every interesting state.

## Debuggability

Three rules that pay off across the whole project:

1. **`deriving Repr` on every type in `Parse/` and `Link/`.** Then
   `--inspect` is `IO.println (repr plan)`. Verbose dumps fall out of
   the structure for free.
2. **Deterministic output.** No timestamps, no hash-iteration order,
   no addresses chosen by ASLR in the plan. Sort everything that has
   no semantic order. Without this, golden tests are useless.
3. **Structured failure messages.** Errors carry the offending
   relocation type, file offset, symbol name, and computed value —
   not just `panic`. Both for human reading and for diff-based
   regression detection.

In addition: print load addresses in `--inspect` output so a developer
can `gdb -p <pid>` against a running load and `b *<addr>`. Use
`dbg_trace` ad hoc during development; `#eval` in the Lean infoview
for parser-level introspection.

## Examples vs tests

Two directories, two roles:

- `examples/` — C sources plus a Makefile that builds real ELF
  binaries with `musl-gcc`. These are the showcase: small programs
  exercising specific loader features (mutual recursion, TLS,
  init_array, etc.). They are the inputs the loader runs against,
  and double as fixture data for tests.
- `Tests/` — Lean test files. Pure `Parse`/`Link` unit tests, golden
  comparisons against `examples/build/*` outputs, and a differential
  driver against the system `ld.so`.

## Testing

Four layers, in increasing fidelity:

1. **Inline unit tests with `#guard`.** Tiny invariants on `Parse`
   and `Link` over hand-crafted byte arrays. Cheap to write, run at
   compile time.
2. **Golden tests against `examples/build/*` outputs.** Capture
   `repr (parse bytes)` and `repr (link input)` to checked-in
   `Tests/golden/*.txt`. Diff on every change. Determinism (rule 2
   under Debuggability) is what makes this work.
3. **Cross-check against `readelf -a`.** A script that diffs
   `Parse` output against `readelf` for the same binary. Catches
   format bugs the synthetic inputs miss.
4. **Differential testing against `ld.so`.** The strongest signal.
   Run LeanLoad on an `examples/` binary, capture mmap layout and
   relocation writes; compare to `ld.so` on the same binary
   (e.g. `LD_DEBUG=files,reloc`). A clean diff is the proof the
   loader behaves like the real one.

Test layout:

```
Tests/
  golden/             checked-in expected outputs
    main.parse.txt
    main.link.txt
  Parse.lean          #guard + golden
  Link.lean           #guard + golden
  Differential.lean   ld.so comparison
  Test.lean           lake test entry point
```

Wired up via `testDriver := "test"` in `lakefile.lean` pointing at a
`lean_exe test`. Run with `lake test`. No external framework needed
in v1.

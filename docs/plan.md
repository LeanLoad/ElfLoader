# Implementation Plan

Five phases. Each ends with a runnable artifact and a check that
gates moving on. Architecture and trust boundary are in `design.md`;
exec/stack design in `exec.md`; proof obligations in `verification.md`.
This file is sequencing.

**Status:** Phases 0–4 done. Phase 5 well underway: multi-object
materialise, relocation application, init_array invocation, full
VeriLoad-style auxv (`AT_PHDR`/`PHENT`/`PHNUM`/`PAGESZ`/`BASE`/`ENTRY`/`RANDOM`/`UID`/`EUID`/`GID`/`EGID`/`HWCAP`/`HWCAP2`/`CLKTCK`/`SECURE`/`EXECFN`/`SYSINFO_EHDR`),
signal-handler reset to `SIG_DFL` before transfer of control (avoids
deadlock in Lean's `segv_handler` ↔ libuv pthread-lock).

Static loader runs end-to-end (`hello from leanload`, rc=42).

Dynamic `build/main`: pipeline parses, discovers, resolves,
plans layouts, materialises 5 objects, applies relocations, runs all
6 shared-library constructors (libfoo ×2, libbaz ×2, libbar ×2),
forks into a clean child, transfers control. Crashes deep inside
musl's `do_init_fini` — musl's `__libc_start_main` walks an internal
"link map" populated by ld.so during dynamic linking; we don't
populate it (we run constructors ourselves), so the walk segfaults.

Bugs fixed along the way:

- `R_AARCH64_GLOB_DAT` for symbols defined locally in the relocating
  object (e.g. libc's `__environ`): we previously fell back to symbol
  value 0 because `Resolve` only tracks undefined references.
  `Reloc.resolveSymValue` now uses `obj.symtab[symIdx].st_value` when
  `st_shndx ≠ SHN_UNDEF`, falling through to the resolution table
  only for true externals.
- Lean's `segv_handler` calling `pthread_getattr_np` deadlocked
  against libuv's pthread lock when the loaded binary faulted. We
  now reset SIGSEGV/SIGBUS/SIGILL/SIGFPE/SIGABRT/SIGPIPE to `SIG_DFL`
  before transfer of control.
- The whole loaded program now runs in a `fork`'d child, leaving
  Lean's threads in the parent. Parent waits for the child and
  forwards its exit status. Mirrors `execve(2)`'s "fresh process"
  semantics from the caller's perspective.

What's left: populate musl's link-map (or use static-pie binaries
that don't need ld.so coordination, or drive ld.so via PT_INTERP).

The example binaries are now built **with** the full musl ld.so
(removed `LDSO_OBJS=`). Both native `exec` (via kernel + musl's
ld.so) and LeanLoad's path are valid loaders for the same binary,
which is what differential testing wants.

## Phase 0 — Scaffold (done)

- `third_party/` submodules.
- `examples/` C fixtures + Makefile producing musl-linked binaries.
- `Tests/` Lean test harness wired to `lake test`.
- `docs/{ffi,design,plan}.md`.

**Exit:** `lake test` passes; `make -C examples` produces
`build/main` that the system loader can run.

## Phase 1 — Parse (pure) ✓ done

Read an ELF file's header structures into typed records. No `IO`,
no FFI. Outputs are `Except String α`.

**Style.** The parser should read like the spec, not like byte
manipulation:

- Types mirror gabi C structs. Field names and order match;
  doc-comment cites the gabi/x86-64-ABI section.
- Parsers are field-by-field, in a `Parser α := StateT Offset (Except String) α`
  monad. Each parser is a `do`-block, one line per field. Endianness
  and bounds live in the primitives.
- Constants for one ELF concept live in that concept's file (no
  separate `Constants/` tree). One file ≈ one gabi chapter.

Sub-steps, each its own commit + golden test:

1. **Parser monad + primitives.** `LeanLoad.Parse.Bytes`:
   `Parser`, `u8`, `u16le`, `u32le`, `u64le`, `slice`, `expectMagic`,
   bounds-checked. Foundation for everything else.
2. **ELF header.** `Parse.Header.parse : ByteArray → Except String ElfHeader64`.
   Reject non-ELF, non-64-bit, non-little-endian, non-x86_64.
3. **Program headers.** `Parse.Program` — the array indexed by
   `e_phoff`/`e_phnum`/`e_phentsize`.
4. **Dynamic section.** `Parse.Dynamic` — walk `PT_DYNAMIC`'s
   contents into a `Dyn64` array. Pull out the tags Plan will need:
   `STRTAB`, `SYMTAB`, `RELA`, `JMPREL`, `INIT`/`FINI`, `INIT_ARRAY`,
   `RUNPATH`/`RPATH`, `NEEDED`.
5. **Strtab + dynsym.** `Parse.Symbol` — given a `ByteArray` and a
   `(offset, size)` pair from the dynamic section, materialize the
   string table and the dynamic symbol array.
6. **Relocations.** `Parse.Reloc` — `.rela.dyn` and `.rela.plt`
   entries. x86-64 reloc-type enum (gabi 06 + x86-64-ABI).
7. **Aggregate.** `Parse.File.parse : ByteArray → Except String ParsedElf`.

**Tests:** `#guard` invariants on hand-crafted byte literals;
golden snapshots of `Parse.File.parse` over `build/{main,libfoo.so,libbar.so,libbaz.so}`;
field-level diff against `readelf -a` for at least the header and
program-header table (smoke-test, not a permanent test fixture).

**Exit:** `Parse.File.parse` round-trips every binary in
`build/`. Goldens checked in.

## Phase 2 — Static loader (minimum viable) ✓ done

> Implementation note: instead of the original "call entry as
> `int (*)(void)`" plan, we built kernel-style exec from the start —
> see `exec.md`. Single mode, matches what `ld.so` does, and the
> fixture uses nolibc's real `_start`/`_start_c`/`main` chain.

Drop dynamic linking entirely. Build a fixture with `musl-gcc -static`
that takes no shared library. Implement just enough of `Plan` and
`Load` to mmap its `PT_LOAD` segments, `mprotect`, and jump to entry.

This phase produces the smallest possible "we ran a binary" demo
and proves out the FFI shape before tackling symbol resolution.

Scope cut:
- No `Discover`, no `Plan.Resolve`, no `Plan.Search`.
- No relocations. (Static binaries with `-static` against musl
  often have zero or only `R_*_RELATIVE` for PIE; pick a
  non-PIE static fixture so the count is zero.)
- No init/fini arrays in v0; `_start` does its own setup if
  the fixture is plain.

What gets built:
- `runtime/region.{h,c}` with `mmap`, `munmap`, `mprotect`, `memcpy`-by-offset.
- `runtime/exec.{h,c}` with `jump_to_entry(uintptr_t addr) -> int`.
- `LeanLoad.FFI.Region`, `LeanLoad.FFI.Exec`.
- `LeanLoad.Plan.Layout` (PT_LOAD layout, base address per
  gabi 07 § Base Address).
- `LeanLoad.Load` orchestration.

Add a fixture: `examples/static.c` → `build/static`.
Build with `musl-gcc -static -no-pie static.c -o static`.

**Exit:** `leanload build/static` prints whatever the
fixture is supposed to print, exits cleanly. `--inspect` dumps a
plan with one or two `PT_LOAD` regions and zero relocations.

## Phase 3 — Discover + symbol resolution ✓ done

Now reintroduce dynamic linking. Implement IO-side discovery and
pure-side resolution. Still no relocations applied.

1. **`LeanLoad.Discover`** (`IO`). Read main, parse, walk
   `DT_NEEDED` transitively. `Plan.Search` (pure) for the path
   resolution: `DT_RUNPATH` → `LD_LIBRARY_PATH` → defaults
   (gabi 08 § Shared Object Dependencies). Returns a
   `LinkMap` mapping path → `ParsedElf`.
2. **`LeanLoad.Plan.Resolve`** (pure). Breadth-first symbol
   resolution per gabi 08. Output: for each (object, symIdx)
   reference, the providing (object, symIdx). Unresolved symbols
   are explicitly enumerated, not fatal.

**Tests:** golden snapshots of the resolution table over
`build/main` (libfoo / libbar / libbaz cycle exercises
the breadth-first walk and the cycle handling).

**Exit:** every reference in `build/main` resolves to a
known provider. Golden checked in.

## Phase 4 — Layout, relocations, init order

Pure, the last verified piece. Output is a complete `LoaderPlan`.

1. **`Plan.Layout`.** Final mmap layout for every loaded object.
   Choose base addresses for PIE/shared (kernel will hand them out
   at `Load` time; the plan picks relative offsets and protection
   bits).
2. **`Plan.Reloc`.** For each relocation entry, compute
   `(target_address, value_to_write, size)` per the x86-64 formula
   table. Cover `R_X86_64_64`, `_PC32`, `_GLOB_DAT`, `_JUMP_SLOT`,
   `_RELATIVE`, `_GOTPCREL`. Skip TLS in v1.
3. **`Plan.Init`.** Build the constructor and destructor lists
   per gabi 08 § Initialization and Termination Functions.
4. **Combine.** `LoaderPlan` = layout + reloc writes + init lists.

**Tests:** golden snapshots over the example binaries; spot-check
relocations by hand against `readelf -r`. Begin shaping the
differential test against `LD_DEBUG=files,reloc` output.

**Exit:** `--inspect build/main` produces a plan that
matches `ld.so`'s mmap layout (within the constraints of base
address differences) and the same set of relocation writes.

## Phase 5 — Load + differential test

Tie `Load` to the FFI shims. Apply relocations to mmap'd memory,
`mprotect`, run init_array, jump to entry, run fini on exit.

Most of the work is already in phase 2 (`Region`, `Exec`); this
phase adds:
- Relocation writer that pokes bytes into mmap'd regions.
- Init/fini orchestration.

The real value of this phase is the differential harness:
- Run `LeanLoad --inspect <bin>` on each `build/*`.
- Run `LD_DEBUG=files,reloc <bin>` against musl's `ld.so`.
- Diff the two. A clean diff is the proof.

Tests: golden + differential. Once the differential test passes
on `build/main`, broaden to additional fixtures.

**Exit:** `leanload build/main` produces the same stdout
as running `build/main` directly, plus the differential
test passes.

## Out of scope for v1

These are real but deferred. Each can land in its own follow-up:

- **TLS** (`PT_TLS`, `R_X86_64_TPOFF*`, `R_X86_64_DTPMOD*`).
  Doable, but it's its own subsystem (TLS template, per-thread
  blocks). Skip until the static and dynamic non-TLS cases work.
- **Lazy binding via PLT.** v1 binds everything at load time
  (eager binding). The PLT is built and resolved up front;
  no `_dl_runtime_resolve` trampoline.
- **RELR-format relocations** (`.relr.dyn`). Requires a separate
  parser and currently disabled by removing
  `-z pack-relative-relocs` from the Makefile.
- **`IFUNC` / `STT_GNU_IFUNC`.** GNU extension, glibc-only;
  musl doesn't emit these, so they don't appear in our
  fixtures.
- **`dlopen` / `dlsym`.** A loader-as-library API is a separate
  surface from "load and run".
- **Non-x86_64 architectures.** Per `design.md`, committed to
  x86-64 ELF64 only.
- **TLSDESC, GNU hash, `.gnu.version_*`.** Modern GNU extensions.
  Match musl's defaults; revisit only if differential tests demand.

## Suggested commit cadence

One sub-step per commit, one test added per commit. The phases
are too large to land as single commits; a typical phase will be
4–10 commits. The exit criteria above are the natural PR
boundaries if you want larger-grained review.

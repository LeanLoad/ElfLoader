# LeanLoad [![CI](https://github.com/ShawnZhong/LeanLoad/actions/workflows/ci.yml/badge.svg)](https://github.com/ShawnZhong/LeanLoad/actions/workflows/ci.yml)

A verified ELF loader in Lean 4. Reads, plans, and runs Linux ELF
binaries (static + dynamically-linked) through a pipeline split into
a **pure middle** (verified core, all under `Parse/` + `Elaborate/`
+ `Plan/`) and two **trusted IO bookends**:

| Stage     | Pure module     | IO bookend                | What it does                                                                                  |
| --------- | --------------- | ------------------------- | --------------------------------------------------------------------------------------------- |
| Parse     | `Parse/*`       | `Parse/RawElf.parse`      | Byte-decode each ELF into `RawElf`; no semantic checks.                                       |
| Elaborate | `Elaborate/*`   | —                         | Validate the bytes, lift to typed enums, group rela by segment, carry `WellFormed` segments and per-segment page-arithmetic invariants on `Segment`. |
| Discover  | `Discover/Graph` + `Discover/Driver` | `Discover.discover` (`Discover/IO`) | BFS over `DT_NEEDED` (dedup by `DT_SONAME`); produce `LoadGraph` with non-emptiness + names-Nodup + deps witnesses.       |
| Resolve   | `Plan/Resolve`  | —                         | Match each undef ref to a providing `(object, symbol)` via `Fin n`-typed `SymRef`; HashMap-indexed for O(1) lookup. |
| Layout    | `Plan/Layout`   | —                         | Pick per-object mmap base; carry sorted-segments witness in the type.                         |
| Reloc     | `Plan/Reloc`    | (folded into `realize`)   | Per-arch formula → `Patch` list; each patch carries the segment-tying `coversRela` witness so `applyPatch` discharges `Region.InRange` with no runtime check. |
| Init      | `Plan/Init`     | (folded into `realize`)   | DFS post-order over deps, then per-object `init_array` resolution → constructor address list. |
| Exec      | —               | `Exec.realize`            | Single IO sweep over layouts/patches/ctors: mmap + zeroout + mprotect + patch writes + ctor calls + stack + jump. |

Every file under `Parse/`, `Elaborate/`, and `Plan/` is pure Lean;
the only IO seams are `Discover` (file reads) and `Exec.realize`
(mmap + writes + control transfer). The mmap-op sequence
(overlay/bssZero/mprotect) is derived inline from each layout's
segments inside `realize` — there's no separate Map planner because
that "planning" was trivial (a function of segment shape) and only
`realize` consumed it.

Targets AArch64 + x86-64 with musl libc. The verified core is pure
Lean.

https://github.com/ShawnZhong/LeanLoad/blob/4f885ee61cfbb39d6359b42f4086aa4c32116342/run.log#L1-L319

## Quick start

```sh
./setup.sh               # one-shot: install system C toolchain, init submodules
./run.sh                 # build leanload + examples, run on build/main
```

Unit-level invariants live as `#guard` blocks in implementation
files (`Discover/Test.lean`, `Plan/Init.lean`, `Example.lean`, …) and
elaborate during `lake build`. The integration test is `./run.sh`
end-to-end against `build/main`.

## Documentation

- [`docs/design.md`](docs/design.md) — pipeline, trust boundary,
  naming conventions, CLI, kernel-style exec, host-process trust
  assumptions.
- [`docs/plan.md`](docs/plan.md) — open work and out-of-scope items.

The audit surface inside the code is `LeanLoad/Parse/` (byte-level
gabi/abi transcriptions) and `LeanLoad/Elaborate/` (typed views with
gabi-mandated invariants carried as `Segment` fields). Safety
predicates over the planned `Array MemoryOp`
(`OverlaysDisjoint` / `OverlaysContained` / `WritesContained` /
`MprotectsContained`) are decidable and checked at the
`Realize.planOps` boundary; `MemoryOp.runSafe` only accepts
witnessed op arrays.

## De facto conventions

LeanLoad follows several conventions that are *not* mandated by gABI
but are universal across glibc / musl / ld.so. We follow them because
real-world programs assume them; deviating would break compatibility.
Where we're *stricter* than the convention (deliberately rejecting
edge cases instead of papering over them), it's called out below.

**Dependency resolution & dedup** (`Discover/`, `runtime.c`)

- **Dedup by `DT_SONAME` — required for every NEEDED-loaded `.so`.**
  We *fail loud* on a SONAME-less library; ld.so falls back to
  realpath/inode. SONAME is universally set by modern linkers
  (`-Wl,-soname,…`); missing it almost always indicates a build
  mistake. (gABI doesn't mandate dedup at all — see `ld.so(8)`.)
- **Main executable's canonical name = path basename.** Executables
  conventionally don't set SONAME (nothing should link against an
  exe); we use `basename(mainPath)`, never consulting SONAME.
- **Search order for NEEDED:** literal-path (if soname contains `/`)
  → `LD_LIBRARY_PATH` → owning object's `DT_RUNPATH`. Matches ld.so.
- **`DT_RPATH` ignored.** Deprecated by gABI in favor of `DT_RUNPATH`.
  ld.so still honours both with quirky precedence rules; we just
  refuse RPATH outright.

**Layout & process startup** (`Plan/`, `Elaborate/Elf.lean`, `Main.lean`)

- **PT_LOAD segments pairwise disjoint.** gABI only mandates sorted
  `p_vaddr` order; non-overlap is de facto. We carry it as a
  validated `NonOverlap` witness on `Elf`.
- **First PT_LOAD covers the ELF header + program-header table with
  `vaddr = offset`.** Convention so `mainBase + phoff` equals the
  kernel's `AT_PHDR` without offset→vaddr translation. Validated as
  `phdrCovered`.
- **4 KiB page size, hardcoded.** Linux x86_64 + AArch64 default.
  AArch64 supports 16/64 KiB pages but musl + most distros use 4 KiB.
  We don't honour `getpagesize()` at runtime.
- **Stack size: 8 MiB.** Matches musl's default. gABI silent.
- **Stack allocated as a separate `mmap`**, not contiguous with the
  loaded image. Implementation choice — simplifies the reservation
  arithmetic. ld.so does the same.
- **`auxv` (AT_PHDR / AT_PHENT / AT_PHNUM / AT_BASE / AT_RANDOM / …)
  forwarded from the host process** via `getauxval`. Matches the
  kernel exec convention `__libc_start_main` expects.
- **Files opened `O_RDONLY | O_CLOEXEC`, never closed.** Held until
  process exit; the loaded program inherits the fd table. Simplifies
  handle ownership; we never need to track refcounts.

**Init / fini** (`Plan/Init.lean`, `Materialize/Build.lean`)

- **Init order = DFS post-order over the dep DAG; fini = its
  reverse.** gABI 08 mandates a *partial* order ("deps before
  dependents") and leaves cycle order undefined. Our DFS post-order
  matches glibc / musl; reverse-init for fini is also their choice.
- **Zero entries in `DT_INIT_ARRAY` / `DT_FINI_ARRAY` skipped as
  no-ops.** gABI leaves them unspecified; glibc / musl skip them.

**Relocations** (`Elaborate/Reloc.lean`, `Materialize/Reloc.lean`)

- **RELA only, not REL.** Toolchains emit RELA for x86_64 + AArch64;
  REL is legacy.
- **`R_*_GLOB_DAT` addend `A` treated as 0.** psABI documents the
  formula as `S + A` for completeness, but linkers emit GLOB_DAT
  with `A = 0`; a nonzero addend would be a malformed link.
- **Strong undef → fail loud at `Plan.Aggregate.ofGraph`.** ld.so
  fails at startup; we fail at planning time (earlier).
- **Weak undef → resolves to 0.** psABI convention.
- **psABI `OVERFLOW_CHECK` enforced per-relocation.** A 32-bit
  relocation that overflows is rejected; ld.so does the same.

**Target ABI restrictions** (rejected at elaborate time, not just
unsupported in silence)

- **ELFCLASS64 + ELFDATA2LSB only.** 32-bit and big-endian inputs
  rejected at elaborate.
- **`Machine` is a closed enum: x86_64 + AArch64.** Other
  architectures rejected at elaborate (no per-arch reloc table).
- **ET_DYN only.** ET_EXEC inputs rejected at elaborate — the
  reserve-then-overlay layout assumes a PIE base.
- **No TLS yet** (deferred — see `docs/plan.md`). The fixture's
  `__thread` test works because musl's pthread bootstrap synthesizes
  TLS state at thread-creation time, not via ELF TLS phdrs.

## Where gABI overspecifies

gABI marks several fields "mandatory" that real loaders don't enforce.
The flip side of "De facto conventions" above: there, gABI is silent
where reality has a convention; here, gABI is strict where reality is
lax. LeanLoad's posture per field is in the bullet.

**`DT_STRSZ` (gABI 08 § Dynamic, "mandatory" for exec + shared)**

- musl's `ldso/dynlink.c` never reads it — `dso->strings` is a bare
  `char*` indexed by `st_name`, trusting NUL termination. glibc reads
  it only in `elf/dl-addr.c` for `dladdr`'s bounds check, not on the
  load path. A `.so` missing `DT_STRSZ` would load fine under both.
- LeanLoad uses it as the pread byte count for `.dynstr`. Absence →
  empty strtab (silent, not an error). See [`Parse/RawElf.lean`'s
  layer-3 strtab read](LeanLoad/Parse/RawElf.lean).

**`DT_HASH` (gABI 08, "mandatory")**

- `--hash-style=gnu` (modern default on most distros) emits only
  `DT_GNU_HASH`, omitting `DT_HASH`. glibc + musl walk GNU-hash chains
  in that case; gABI never mentions `DT_GNU_HASH` at all.
- LeanLoad sidesteps by requiring `--hash-style=both` in the Makefile
  so `DT_HASH.nchain` is always available as the symtab count (the
  only section whose size doesn't pair with a `DT_*SZ` tag).

**`DT_RELAENT` / `DT_SYMENT` / `DT_PLTREL` (gABI 08, "mandatory")**

- Entry-size tags. Every loader hardcodes the sizes (24 / 24 / 8)
  because they're fixed by gABI itself — reading them would be
  circular. LeanLoad does the same: `RawRelaSize`, `RawSymSize`,
  `RawDynSize` are compile-time constants; the tags are ignored.

**Section headers (gABI 03)**

- gABI describes section headers extensively, but loaders don't need
  them at all — only `.dynamic` matters at load time. `strip
  --strip-all` removes them; many production binaries ship without.
- LeanLoad strips them too: the fixture sets `e_shoff = 0`, and the
  parser never reads section headers — only the program-header table
  + `.dynamic`.

**`DT_RPATH` "deprecated" (gABI 08)**

- gABI deprecates `DT_RPATH` in favor of `DT_RUNPATH`, but ld.so still
  honors both with quirky precedence rules. So "deprecated in gABI"
  understates how alive it is in practice.
- LeanLoad takes the stricter line — `DT_RPATH` is refused outright
  (see "De facto conventions" above, `Discover/`).

**`EI_OSABI` / `EI_ABIVERSION` (gABI 02)**

- gABI says these identify the target OS ABI; Linux's loader ignores
  the values in practice.
- LeanLoad parses but doesn't validate against an allowlist.

## Module layout

```
LeanLoad.lean              package root (re-exports)
Main.lean                  CLI executable entry — Lake-blessed top-level placement
LeanLoad/
  Parse/                   byte decoders — Elf64_* C-struct transcriptions
    Decode.lean            parser monad (cursor + Except, u32le / u64le primitives)
    Deriving.lean          `deriving BytesDecode` handler — auto field-by-field decode
    Structs.lean           Raw{Ehdr,Phdr,Sym,Rela,Dyn,…} structs + DT_*/PT_* tag constants
    Dynamic.lean           .dynamic decoder + tag-keyed lookups (find?, findAll, pair?)
    RawElf.lean            top-level `parse` (header → phdrs → .dynamic → strtab → …)
  Elaborate/               typed semantic views over Parse — validates and enriches
    Header.lean            ElfType / Machine enums; ELFCLASS64 / ELFDATA2LSB constants
    Strtab.lean            NUL-terminated UTF-8 lookup by offset
    Symbol.lean            SymBind / ShnIdx enums + `Symbol` (name pre-resolved)
    Reloc.lean             PatchSize (b4/b8); per-arch formula tables; `formulaFor` dispatch
    Segment.lean           gabi-07 segment with per-segment invariants
                           (fileszLeMemsz / alignPow2 / alignCong / addrBound) +
                           page-aligned views + per-segment rela arrays
    Elf.lean               `Elf` aggregate (with Sorted/NonOverlap PT_LOAD witnesses);
                           `elaborate : RawElf → Except String Elf` (rejects ET_EXEC)
  Plan/                    pure middle — every stage that produces abstract data
    Resolve.lean           SymRef n / Unresolved n / Table n with O(1) HashMap index
    Layout.lean            assignBases (base parameter, kernel-picked in production);
                           totalSpan; per-Region page math; segmentsSorted validation
    Reloc.lean             planRela / planObject / plan emit `MemoryOp.write` ops
                           (4 or 8 bytes) with psABI 32-bit overflow check
    Init.lean              buildDeps (HashMap O(N+E)) + DFS post-order + ctor address list
    Realize.lean           Region.ops (per-segment mmapFile/zeroout/mprotect);
                           realizeOps + planOps with decidable safety predicates
  Discover/
    Graph.lean             LoadedObject + LoadGraph (BFS state carrier with
                           non-emptiness / names-Nodup / deps-shape / deps-bounds
                           witnesses) + smart constructors recordDep / appendChild
    Effects.lean           abstract IO leaf (resolveDep + fail), monad-polymorphic;
                           instantiated by IO.lean (production) and Test.lean (pure)
    Driver.lean            WorkItem / Decision / dispatch + BfsState +
                           linkExisting / appendAndQueue helpers + step +
                           discoverLoopWith
    IO.lean                Effects.io (Runtime.openByName → parseFromHandle) +
                           discover (production entry; opens main, drives BFS)
    Test.lean              Effects.test (over in-memory TestStore) + discoverPure +
                           #guard scenarios (linear/diamond/cycle/SONAME/search-order)
  Runtime.lean             @[extern] trust seam — FileHandle, mmap (file overlay),
                           mmapAnonAlloc (kernel-picked reservation), mprotect,
                           write, zeroout, mmapStack, callCtor, execAndJump;
                           MemoryOp inductive + safety predicates + runSafe
  Example.lean             cross-stage `#guard` walkthrough (synthetic fixtures)
runtime/
  Runtime.c                C shims (open / pread / mmap variants / mprotect /
                           write / zeroout / mmapStack / callCtor / execAndJump)
docs/                      design.md · plan.md
examples/                  C sources for showcase binaries (PIE main + libfoo/bar/baz)
third_party/               submodules (musl, gabi, …)
```

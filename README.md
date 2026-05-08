# LeanLoad [![CI](https://github.com/ShawnZhong/LeanLoad/actions/workflows/ci.yml/badge.svg)](https://github.com/ShawnZhong/LeanLoad/actions/workflows/ci.yml)

A verified ELF loader in Lean 4. Reads, plans, and runs Linux ELF
binaries (static + dynamically-linked) through a pipeline split into
a **pure middle** (verified core, all under `Parse/` + `Elaborate/`
+ `Plan/`) and two **trusted IO bookends**:

| Stage     | Pure module     | IO bookend                | What it does                                                                                  |
| --------- | --------------- | ------------------------- | --------------------------------------------------------------------------------------------- |
| Parse     | `Parse/*`       | `Parse/RawElf.parse`      | Byte-decode each ELF into `RawElf`; no semantic checks.                                       |
| Elaborate | `Elaborate/*`   | —                         | Validate the bytes, lift to typed enums, group rela by segment, carry `WellFormed` segments and per-segment page-arithmetic invariants on `Segment`. |
| Discover  | `Plan/Discover` | `Discover.discover`       | Walk `DT_NEEDED`, BFS-dedup; produce non-empty `ObjectList`.                                  |
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
./test.sh                # build examples + run the Lean test suite
```

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

## Status

- Dynamic binary (musl-linked, multi-shared-object closure, PIE):
  runs end-to-end against `examples/build/main`. ET_DYN-only —
  ET_EXEC inputs are rejected at elaborate time.
- Differential tests against `ld.so` are not yet wired up.

## Module layout

```
LeanLoad.lean              package root (re-exports)
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
    Plan.lean              ObjectList non-empty subtype; LoadedObject; BFS dedup
    IO.lean                walk DT_NEEDED via IO; resolve filenames against runpath
  Runtime.lean             @[extern] trust seam — FileHandle, mmap (file overlay),
                           mmapAnonAlloc (kernel-picked reservation), mprotect,
                           write, zeroout, mmapStack, callCtor, execAndJump;
                           MemoryOp inductive + safety predicates + runSafe
  Main.lean                CLI + load / debug orchestration; calls mmapAnonAlloc once,
                           threads base into pure planning, dispatches via runSafe
  Example.lean             cross-stage `#guard` walkthrough (synthetic fixtures)
  Test.lean                test exe entry — runs every pure stage on the real fixture
runtime/
  Runtime.c                C shims (open / pread / mmap variants / mprotect /
                           write / zeroout / mmapStack / callCtor / execAndJump)
docs/                      design.md · plan.md
examples/                  C sources for showcase binaries (PIE main + libfoo/bar/baz)
third_party/               submodules (musl, gabi, …)
```

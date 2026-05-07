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

https://github.com/ShawnZhong/LeanLoad/blob/7db77ebd080827228f5376478ee5db3e3f12c0a5/run.log#L1-L320

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

The audit surface inside the code is `LeanLoad/Parse/` (byte-level
gabi/abi transcriptions) and `LeanLoad/Elaborate/` (typed views with
gabi-mandated invariants carried as `Segment` fields). Cross-stage
theorems (`bss_inRange`, `patch_inRange`, `inRange_4_of_8`,
`assignBases_size`, `segment_endAddr_le_objectSpan`,
`segmentsPairwiseDisjoint_of_segmentsSorted`) live alongside the
constructions they discharge in `LeanLoad/Plan/Layout.lean`.

## Status

- Static binary (no libc): runs end-to-end via `leanload examples/build/static`.
- Dynamic binary (musl-linked, multi-shared-object closure): runs
  end-to-end against `examples/build/main`.
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
    RawSegment.lean        gabi-07 spec-level segment: byte-fields + per-segment invariants
                           (fileszLeMemsz / alignPow2 / alignCong) + 48-bit addrBound +
                           per-segment rela arrays
    Segment.lean           extends `RawSegment` with loader-stage page-aligned views
                           (pageVaddr / pageLength / fileLenPaged / …) + pre-discharged
                           arithmetic invariants (`pageVaddr_le_vaddr`, `insetMemszLePageLength`)
    WellFormed.lean        multi-segment Sorted + NonOverlap, decidable
    Elf.lean               `Elf` aggregate + `elaborate : RawElf → Except String Elf`
  Plan/                    pure middle — every stage that produces abstract data
                           (theorems for the IO-bookend live alongside their construction)
    Discover.lean          BFS dedup + LoadedObject + ObjectList (non-empty subtype)
    Resolve.lean           SymRef n / Unresolved n / Table n with O(1) HashMap index
    Layout.lean            ObjectLayout; assignBases (sized output); `g.layouts` validator;
                           bss_inRange / patch_inRange / segmentsPairwiseDisjoint
    Reloc.lean             Patch g (Fin segIdx + coversRela witness) + PatchSize dispatch
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

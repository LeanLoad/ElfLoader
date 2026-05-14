# LeanLoad Design

Verified ELF loader in Lean 4. The verified core is pure Lean; the
syscall layer sits behind one small `@[extern]` module
(`LeanLoad/Runtime.lean`) plus C shims under `runtime/`.

## Stages

Pipeline (one row per `--debug` section):

| Stage           | Type | Input → Output                                                                       |
| --------------- | ---- | ------------------------------------------------------------------------------------ |
| **Parse**       | IO   | `FileHandle` → `RawElf` (per-section `pread`s; bytes only, no semantic checks)       |
| **Elaborate**   | pure | `RawElf` → `Except String Elf` (gabi-07 invariants discharged as `Segment`/`Elf` fields) |
| **Discover**    | IO   | `path → LoadGraph` (BFS over `DT_NEEDED`; calls Parse + Elaborate per file; deps recorded inline) |
| **Plan**        | pure | `LoadGraph → Plan` (resolve table + per-elf `Layout` + `initOrder`)               |
| **Materialize** | pure | `BoundPlan → { lo : LoadOps n // Safe rsv.addr rsv.len lo }` (typed slot tree + structural safety) |
| **Runtime**     | IO   | witnessed `LoadOps` → `IO Unit` (mmap + zeroout + mprotect + reloc stores + ctor calls + stack + jump; no return) |

`BoundPlan extends Plan` (Lean structure inheritance) with `rsv :
Reserve` and `h_total : rsv.len = layout.totalSpan`. Constructed once
in `Main.load` via `{ plan with rsv, h_total }` after `Reserve.run`
allocates the kernel-picked anon block. Consumers access planning
fields directly (`bp.layout`, `bp.objects`, …) — no `bp.plan.X`
indirection. The reservation bounds every safety predicate in
`Materialize`.

### Plan stage — three internal sub-phases

`Plan.ofObjects : LoadGraph → Except String Plan` runs three sub-phases
in sequence. They could in principle be top-level stages, but bundling
them keeps the stage count manageable; the `Plan/` directory makes the
breakdown discoverable:

| Sub-phase | Module             | Produces                                       | Can fail?                                |
| --------- | ------------------ | ---------------------------------------------- | ---------------------------------------- |
| Resolve   | `Plan/Resolve.lean`| `Resolve.Table` (per-undef BFS lookup)         | yes — strong-undef rejected at top level |
| Layout    | `Plan/Layout.lean` (uses `Plan/SegmentLayout.lean`) | per-segment + per-elf + cumulative layout | yes — page-aligned overlap or cumulative span overflow |
| Init      | `Plan/Init.lean`   | DFS post-order over `g.deps`                   | no — total                               |

Reloc planning runs *inside* Layout: each `SegmentLayout`'s `relocs`
field is filled by `Plan.Reloc.planSegment` while the layout is being
built. Bake (turning `Reloc.Entry` into `StoreOp`) lives separately
in `Materialize/Reloc.lean` and runs base-aware.

## Key types

| Type                          | Module                       | Contract                                                                                  |
| ----------------------------- | ---------------------------- | ----------------------------------------------------------------------------------------- |
| `Parser α`                    | `Parse.Decode`               | Stateful read; advances the cursor or returns `Except`.                                   |
| `Parse.RawElf`                | `Parse.RawElf`               | Per-file byte decode (header, phdrs, strtab, symtab, needed, soname, runpath, rela, jmprel, init/fini arrays). |
| `Elaborate.Segment`           | `Elaborate.Segment`          | One PT_LOAD with gabi-07 invariants (`fileszLeMemsz`, `alignPow2`, `alignCong`, `addrBound`) + per-segment relocs in `coversRela` subtype. |
| `Elaborate.Elf`               | `Elaborate.Elf`              | Per-elf bundle with `Sorted` / `NonOverlap` / `PhdrCovered` / `CtorsInExecSeg` witnesses. |
| `Discover.LoadGraph`         | `Discover.Step`              | Loaded objects in BFS order + `sizePos` / `namesNodup` / `deps` (recorded during BFS).    |
| `Resolve.SymRef n`            | `Plan.Resolve`               | Resolved symbol `(objectIdx : Fin n, symIdx : Nat)`.                                      |
| `Plan.SegmentLayout n`          | `Plan.Layout`                | One `Segment` lifted with page math + 5 per-segment Prop fields (`pageEnd_lt`, …) + per-segment relocs. |
| `Plan.ElfLayout n`              | `Plan.Layout`                | One elf's `SegmentLayout`s + `advance` + cross-segment proofs (`segmentsSorted`, `pageEndAddr_le_advance`). |
| `Plan.Layout n`             | `Plan.Layout`                | All elves' `ElfLayout`s + cumulative `totalSpan` + `totalSpan_eq` Nat↔UInt64 bridge.        |
| `Reloc.Entry n seg`      | `Plan.Reloc`                 | One planned relocation, base-free, with `coversRela` witness inherited from `Segment`.    |
| `Reloc.Formula`               | `Elaborate.Reloc`            | `(type, S, A, B, P) → Option write`. Pluggable per-arch.                                  |
| `Plan.Aggregate`                   | `Plan.Aggregate`             | `objects + resolve + layout + initOrder`, all indexed at `objects.val.size`.              |
| `Materialize.BoundPlan`       | `Materialize.BoundPlan`      | `extends Plan with rsv : Reserve, h_total`. Canonical input to `Materialize.build`. Inherits `bp.objects`, `bp.layout`, etc. |
| `Materialize.SegmentOps n`    | `Materialize.LoadOps`        | Per-segment slot bundle: `(plan, mmap?, zero?, stores, mprotect)`.                        |
| `Materialize.LoadOps n`       | `Materialize.LoadOps`        | `Array (ElfOps n)` — the structured op tree consumed by `runSafe`.                        |
| `Materialize.SetupOps`      | `Materialize.LoadOps`        | Per-segment setup slot record `{ mmap?, zero?, mprotect }` returned by `setupOps`.      |
| `Materialize.LoadSafe`        | `Materialize.Safety`         | Tree-shaped safety witness (per-segment InRange + within-/cross-elf disjoint). `runSafe` accepts only witnessed `LoadOps`. |
| `MmapOp` / `ZeroOp` / `StoreOp` / `MprotectOp` / `Reserve` | `Runtime` | Typed records wrapping each FFI signature.                                            |

## Witness flow

Each stage adds either data or a Prop witness; once witnessed, no
downstream stage re-checks. The chain:

```
Parse:       bytes → RawElf
Elaborate:   RawElf → Elf       + Segment.{fileszLeMemsz, alignPow2,
                                            alignCong, addrBound, coversRela}
                                 + Elf.{segmentsSorted, segmentsNonOverlap,
                                         phdrCovered, initArrInExecSeg,
                                         finiArrInExecSeg}
Discover:    path → LoadGraph  + sizePos, namesNodup, depsSize, depsBounds
Plan:        LoadGraph → Plan  + per-SegmentLayout (pageEnd_lt /
                                  fileOverlay_le_pageLength /
                                  vaddr_memsz_le_pageEnd /
                                  zero_end_le_pageLength /
                                  pageInset_eq_vaddr)
                                 + ElfLayout (segmentsSorted,
                                            pageEndAddr_le_advance)
                                 + Layout (elfs_size, totalSpan_eq)
                                 + Resolve.Table.entries discharges no
                                   strong-undef remains (rejected at
                                   ofObjects)
Materialize: BoundPlan → { lo : LoadOps n // Safe lo }
                                 (every slot witnessed in-range, mmaps
                                  pairwise disjoint — chained from
                                  BoundPlan's per-(i,j) theorems)
Runtime:     witnessed lo → IO Unit
                                 (FFI dispatch; no further checks)
```

## Trust boundary

- **Verified (pure Lean, no IO, no `@[extern]`):**
  `LeanLoad/Parse/`, `LeanLoad/Elaborate/`, `LeanLoad/Plan/`,
  `LeanLoad/Materialize/` (excluding the IO interpreter at the bottom of
  `Materialize/LoadOps.lean`).
- **Trusted:**
  - `runtime/*.c` — audited C shims (~150 lines).
  - `LeanLoad/Runtime.lean` — `@[extern]` declarations + the typed slot
    records' `run` methods + `Reserve.run`.
  - IO bookends: `LeanLoad/Discover/IO.lean`, `LeanLoad/Main.lean`,
    plus `LoadOps.runSafe` (which only accepts a `Safe`-witnessed tree
    but the FFI dispatch itself isn't proved).

A grep for `@[extern]` outside `LeanLoad/Runtime.lean` is a smell.

## Naming conventions

- **`Parse/X.lean`** — byte decoders. One struct per ELF C type
  (`Elf64_*`); the def *is* the format. Auto-derived `BytesDecode`
  instances walk fields in order.
- **`Elaborate/X.lean`** — typed semantic views over Parse. Validates
  bytes, lifts to closed enums, and carries gabi-mandated invariants
  as Prop fields.
- **Lean module ↔ C file** — `LeanLoad/Runtime.lean` ↔
  `runtime/runtime.c`. Extern symbols prefixed `leanload_<topic>_<op>`
  (e.g. `leanload_mmap_anon`, `leanload_exec_run`) so the flat C
  namespace doesn't collide.
- **Opaque Lean types named for what they are** (`Reserve`, not
  `ReservePtr`).
- **Per-stage namespaces** — `LeanLoad.Parse`, `LeanLoad.Elaborate`,
  `LeanLoad.Discover`, `LeanLoad.Plan`, `LeanLoad.Plan.Resolve`,
  `LeanLoad.Plan.Reloc`, `LeanLoad.Plan.Init`, `LeanLoad.Materialize`,
  `LeanLoad.Runtime`. File path matches namespace.

## Scope

**Architecture: AArch64 and x86-64.** Concrete struct types
(`Elf64_Ehdr`, `Elf64_Phdr`, `Elf64_Sym`, `Elf64_Rela`); no
32-bit / typeclass abstraction layer. The reloc planner is parametric
over a per-arch `Formula` type; per-arch tables live in
`LeanLoad/Elaborate/Reloc.lean` and `formulaFor` dispatches on
`e_machine`.

**Parser scope: loader-minimal.** A loader does not need to parse
the full ELF, only what is reachable from program headers and the
dynamic section.

- Parsed: ELF header; program header table; `PT_DYNAMIC` and the
  `.dynamic` array; dynsym + dynstr (size derived from `DT_HASH`'s
  `nchain`); `Rela` and `JMPREL` tables; init/fini arrays.
- Skipped: section headers, `.text`/`.bss`/`.rodata` section
  metadata, debug info.

**Binary type: ET_DYN only.** ET_EXEC inputs are rejected at elaborate
time.

## CLI

```
leanload <elf>             # load and run; does not return
leanload --debug <elf>     # same as `load`, with stage-by-stage prints
```

`--debug` runs the full pipeline (mmap, relocate, run ctors, transfer
control) but prints a header and summary per stage so a developer can
see which stage misbehaves if the loaded image crashes. The dump shows
discovered objects, layouts, init/fini order, and planned ops.

## Debuggability

Three rules that pay off across the project:

1. **`deriving Repr` on every parse / elaborate / plan type.**
   Then `--debug` is structured by construction.
2. **Deterministic output.** No timestamps, no hash-iteration order,
   no addresses chosen by ASLR in the plan. Sort everything that has
   no semantic order — golden tests rely on this.
3. **Structured failure messages.** Errors carry the offending
   relocation type, file offset, symbol name, and computed value —
   not just `panic`.

## Tests vs. theorems

Both have a job, and adding one doesn't retire the other:

- **`#guard` checks** colocated with each definition serve *readers*.
  Concrete examples like
  `formula R_X86_64_RELATIVE { B := 0x10000, A := 0xa90, … } = some { value := 0x10a90, size := .b8 }`
  make a function's contract scannable and fail at elaboration time
  if the table moves under them. Use them anywhere a function does
  nontrivial arithmetic, table lookups, formula evaluation, or
  has interesting edge cases (empty inputs, alignment boundaries,
  symbol-less relocations).
- **Theorems live next to the definitions they characterise.**
  `Plan/Layout.lean`'s `raw_*` lemmas discharge the per-`SegmentLayout`
  invariants; `Materialize/BoundPlan.lean`'s `segment_*_in_rsv` and
  `*_disjoint` theorems power the structural `Safe` proof in
  `Materialize/Build.lean`. There is no separate `Thm/` tree — the
  proofs live with the code they're about.

A `#guard` shows *what the function does* on a concrete input; the
theorem shows *what it always does*. The two are complementary
audit surfaces.

## Trust assumptions on the host process

LeanLoad performs in-process loading: the loaded binary's segments
are `mmap`'d into leanload's own address space, and the trampoline
hands off without first replacing the process image. The IO load
path (`Discover.IO` + `Materialize` + `Runtime` + `Main.realize`) is
conditioned on:

1. **Address-space disjointness.** The reservation returned by
   `mmapAnon` does not intersect any mapping currently in use by
   leanload itself. The kernel's anon-mmap guarantees this.
2. **No concurrent address-space mutation.** No other thread calls
   `mmap` / `munmap` / `mprotect` / `mremap` during materialize→exec.
3. **No locks held across the trampoline.** No host thread holds
   a libc internal mutex (malloc arena, dynamic-loader lock, …) that
   the loaded binary will then try to acquire.
4. **Loaded binary uses `__NR_exit_group`, not `__NR_exit`.** The
   thread-scoped `exit` syscall would only kill the calling thread;
   other host threads survive and the process never terminates.
   musl's `_exit` does the right thing.
5. **Signal handlers reset to `SIG_DFL`** before transfer of control,
   so the loaded binary's faults do not wake Lean's `segv_handler`
   (which deadlocks against libuv's pthread lock).

Differential testing is the right time to revisit these, either by
forking a single-threaded child before loading or by proving
fixture-specific instances of the assumptions.

## Memory ownership

- **Inputs** (ELF files): held open as `Runtime.FileHandle`s for the
  loader's lifetime. Per-section `pread`s — no whole-file `ByteArray`
  is constructed.
- **Reservation** (per loaded binary): one `Reserve.run` IO call
  returns a kernel-picked anon block of size `lp.totalSpan`. Every
  per-elf base sits inside it; every safety predicate is bounded by
  it.
- **Outputs** (loaded image): file overlays mmap'd on top of the
  reservation; partial-page BSS zeroed in place; `mprotect`'d to
  final permissions. Mappings live for the process lifetime; the
  kernel reclaims at exit.

## Kernel-style exec

The trampoline (`Runtime.execAndJump` → `runtime/exec.c`) builds the
same stack `execve(2)` would (argc/argv/envp/auxv at SP, strings
above) and jumps to `e_entry`. SP is 16-byte aligned (AArch64 ABI +
SysV x86-64 § Initial Stack and Register State). Per-arch trampolines:
AArch64 `mov sp, _; br _` and x86-64 `movq _, %rsp; xor rbp; xor rdx;
jmpq *_`. No return: leanload's process *is* the loaded program after
the jump.

Three non-obvious gotchas:

1. **Auxv must forward host-process values.** `AT_RANDOM`,
   `AT_HWCAP`, `AT_HWCAP2`, `AT_CLKTCK`, `AT_SECURE`,
   `AT_SYSINFO_EHDR`, `AT_UID`/`AT_EUID`/`AT_GID`/`AT_EGID` are
   pulled via `getauxval` and copied through. musl's
   `__libc_start_main` crashes without them in feature-detection,
   identity, or vDSO setup.
2. **Signal handlers are reset to `SIG_DFL`** before the jump
   (`SIGSEGV`/`SIGBUS`/`SIGILL`/`SIGFPE`/`SIGABRT`/`SIGPIPE`).
   Otherwise faults in the loaded binary wake Lean's `segv_handler`,
   which calls `pthread_getattr_np` and deadlocks against libuv's
   pthread lock (Lean's threads are still alive).
3. **The loaded program must call `__NR_exit_group`, not
   `__NR_exit`.** Lean's runtime threads coexist with the loaded
   program; a thread-scoped `_exit` leaves them alive and the
   process hangs. musl's `_exit` does the right thing.

# LeanLoad Design

Verified ELF loader in Lean 4. The invariant-carrying core is Lean; syscall
effects sit behind `LeanLoad/Runtime/{FileOps,MemoryOps,ExecOps}.lean` plus C
shims in `LeanLoad/Runtime.c`.

See `AGENTS.md` for working-style guidance.

## Pipeline

| Stage           | Type     | Input → Output                                                                       |
| --------------- | -------- | ------------------------------------------------------------------------------------ |
| **Parse**       | monadic  | `Runtime.FileOps m h → h → ExceptT String m Elf` — bytes plus gabi-07 invariants on `Segment` / `Elf` |
| **Discover**    | monadic  | `ObjectFinder m → Nat → String → m LoadGraph` — DFS over `DT_NEEDED`; deps + init order recorded inline |
| **Reloc**       | pure     | `LoadGraph → Reloc.Result` — relocation-driven symbol resolution                       |
| **Layout**      | pure     | `Reloc.Result → Layout` — per-elf placement + cumulative span                         |
| **Finalize**    | pure     | `BoundPlan → LoadOps rsv.addr rsv.len n` — intrinsic-safe ops                         |
| **Runtime**     | IO       | intrinsic-safe `LoadOps → IO Unit` — mmap + zero + reloc stores + mprotect + ctor + jump; no return |

Production passes `ObjectFinder.io` to the monadic `Discover.discover`: open/parse
the main object and use the same finder for path search + dependency parsing.
Reloc runs relocation-driven BFS lookup (strong referenced undef rejected), then
Layout computes per-segment, per-elf, and cumulative placement. Init order is
computed during Discover's DFS and lives on `LoadGraph.initOrder`.

## Witness flow

Each stage adds either data or a Prop witness; no downstream stage
re-checks.

- **Parse**: per-`Segment` gabi-07 invariants + per-`Elf` (sorted,
  non-overlap, phdr-covered, callable-targets-in-exec-seg).
- **Discover**: `LoadGraph` carries `sizePos`, `namesNodup`,
  `depsSize`, `depsBounds`, `closure`, `initOrderSize`, `initOrderCovers`,
  and `initOrderNodup`; `LoadGraph.InitOrderRespectsDeps` witnesses every
  recorded `DT_NEEDED` edge as dependency-before-dependent in `g.initOrder`.
  Cycles are rejected during discovery because gabi 08 leaves cyclic init
  ordering undefined.
- **Reloc**: relocation-driven symbol resolution; discharges referenced
  unresolved strong symbols.
- **Layout**: per-`SegmentLayout` page-math invariants; `ElfLayout`
  segment-sorting + advance; `Layout` cumulative span.
- **Finalize**: intrinsic-safe `LoadOps` — every op in-range, mmaps pairwise
  disjoint.
- **Runtime**: capability dispatch on the intrinsic-safe tree; no further
  pure-stage checks.

## Trust boundary

- **Verified** (Lean, no direct `@[extern]`): `Parse/`, `Discover/`
  (excluding `Discover/IO.lean`), `Reloc/`, `Layout/`, `Finalize/`
  and `Runtime/Basic.lean`.
- **Trusted**: `LeanLoad/Runtime.c` (~150 lines of audited C shims),
  `LeanLoad/Runtime/{FileOps,MemoryOps,ExecOps}.lean` (FFI declarations +
  concrete IO capability values), `LeanLoad/Runtime/Run.lean`, and the IO
  bookends (`Discover/IO.lean`, `Main.lean`).

## Scope

- **Architecture**: AArch64 and x86-64. Concrete `Elf64_*` struct
  types; reloc planner parametric over `Formula`; `formulaFor`
  dispatches on `e_machine`.
- **Parser**: loader-minimal — ehdr, phdrs, `PT_DYNAMIC`, dynsym +
  dynstr (size from `DT_HASH.nchain`), rela / JMPREL, init/fini
  arrays. Section headers and debug info skipped.
- **Binary type**: ET_DYN only.

## CLI

```
leanload <elf>             # load and run; does not return
leanload --debug <elf>     # same, with stage-by-stage prints
```

The `--debug` dump shows discovered objects, layouts, init/fini
order, and planned ops.

## In-process loading

LeanLoad loads in-process: the binary's segments are `mmap`'d into
leanload's own address space, and the trampoline (`Runtime.ExecOps.execAndJump`
→ `leanload_exec_and_jump` in `LeanLoad/Runtime.c`) hands off without
replacing the process image.
The IO load path is conditioned on:

1. **Address-space disjointness** — `mmapAnon`'s reservation doesn't
   intersect existing leanload mappings (kernel anon-mmap guarantees).
2. **No concurrent address-space mutation** between reservation and jump.
3. **No libc locks held across the trampoline.**
4. **Loaded binary uses `__NR_exit_group`** — thread-scoped `_exit`
   would leave Lean's runtime threads alive.
5. **Signal handlers reset to `SIG_DFL`** before transfer of control
   — otherwise loaded-binary faults wake Lean's `segv_handler`
   (deadlocks against libuv's pthread lock).

The trampoline builds the same stack `execve(2)` would (argc/argv/
envp/auxv at SP, strings above) and jumps to `e_entry`. SP is
16-byte aligned. Auxv (`AT_RANDOM`, `AT_HWCAP`/`HWCAP2`, `AT_CLKTCK`,
`AT_SECURE`, `AT_SYSINFO_EHDR`, `AT_UID`/`EUID`/`GID`/`EGID`) is
forwarded from the host process via `getauxval`; musl's
`__libc_start_main` crashes without it.

## Memory ownership

- **ELF files**: held open as `Runtime.File` for the loader's
  lifetime. Per-section `pread`s — no whole-file `ByteArray`.
- **Reservation**: one `Runtime.MemoryOps.reserve` per loaded binary returns a
  kernel-picked anon block of size `layout.totalSpan`. Every per-elf base sits
  inside it; every emitted op carries an in-reservation proof.
- **Loaded image**: file overlays mmap'd on top of the reservation;
  partial-page BSS zeroed in place; `mprotect`'d to final perms.

## Out of scope

- **TLS** (`PT_TLS`, TLS relocs, TLSDESC) — its own subsystem.
- **Lazy binding via PLT** — eager-bind everything at load time.
- **RELR-format relocations** — disabled by not passing
  `-z pack-relative-relocs`.
- **`IFUNC` / `STT_GNU_IFUNC`** — GNU extension; musl doesn't emit.
- **`dlopen` / `dlsym`** — loader-as-library is a separate surface.
- **GNU-only hash, `.gnu.version_*`** — match musl defaults.
- **Other architectures** — adding a machine is one new file +
  `formulaFor` dispatch.
- **Abstract `mmap` / `mprotect` semantics** — trusted by inspection
  today; research-tier.

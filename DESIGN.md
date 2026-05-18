# LeanLoad Design

Verified ELF loader in Lean 4. Verified core is pure Lean; the
syscall layer sits behind one `@[extern]` module
(`LeanLoad/Runtime.lean`) plus C shims under `runtime/`.

See `AGENTS.md` for working-style guidance.

## Pipeline

| Stage           | Type | Input → Output                                                                       |
| --------------- | ---- | ------------------------------------------------------------------------------------ |
| **Parse**       | IO   | `FileHandle → RawElf` — per-section `pread`s; bytes only                              |
| **Elaborate**   | pure | `RawElf → Except String Elf` — gabi-07 invariants on `Segment` / `Elf`                |
| **Discover**    | IO   | `path → LoadGraph` — DFS over `DT_NEEDED`; deps + init order recorded inline          |
| **Plan**        | pure | `LoadGraph → Plan.Aggregate` — resolve table + per-elf `Layout`                        |
| **Materialize** | pure | `BoundPlan → { lo : LoadOps n // Safe rsv.addr rsv.len lo }`                          |
| **Runtime**     | IO   | witnessed `LoadOps → IO Unit` — mmap + zeroout + mprotect + reloc + ctor + jump; no return |

Plan runs Resolve (per-undef BFS lookup; strong-undef rejected) then
Layout (per-segment + per-elf + cumulative; rejects page-aligned
overlap or `totalSpan` overflow). Init order is computed during
Discover's DFS and lives on `LoadGraph.initOrder`. Reloc planning
runs inside Layout.

## Witness flow

Each stage adds either data or a Prop witness; no downstream stage
re-checks.

- **Elaborate**: per-`Segment` gabi-07 invariants + per-`Elf` (sorted,
  non-overlap, phdr-covered, ctors-in-exec-seg).
- **Discover**: `LoadGraph` carries `sizePos`, `namesNodup`,
  `depsSize`, `depsBounds`, `closure`.
- **Plan**: per-`SegmentLayout` page-math invariants; `ElfLayout`
  segment-sorting + advance; `Layout` cumulative span. `Resolve.Table`
  discharges no strong-undef.
- **Materialize**: `LoadSafe` — every op in-range, mmaps pairwise
  disjoint.
- **Runtime**: FFI dispatch on a `Safe`-witnessed tree; no further
  checks.

## Trust boundary

- **Verified** (pure Lean, no IO, no `@[extern]`): `Parse/`,
  `Elaborate/`, `Plan/`, `Materialize/` (excluding the IO interpreter
  at the bottom of `Materialize/LoadOps.lean`).
- **Trusted**: `runtime/*.c` (~150 lines of audited C shims),
  `LeanLoad/Runtime.lean` (FFI declarations + `run` methods +
  `Reserve.run`), and the IO bookends (`Discover/IO.lean`,
  `Main.lean`, `LoadOps.runSafe`).

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
leanload's own address space, and the trampoline (`Runtime.execAndJump`
→ `runtime/exec.c`) hands off without replacing the process image.
The IO load path is conditioned on:

1. **Address-space disjointness** — `mmapAnon`'s reservation doesn't
   intersect existing leanload mappings (kernel anon-mmap guarantees).
2. **No concurrent address-space mutation** during materialize→exec.
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

- **ELF files**: held open as `Runtime.FileHandle` for the loader's
  lifetime. Per-section `pread`s — no whole-file `ByteArray`.
- **Reservation**: one `Reserve.run` per loaded binary returns a
  kernel-picked anon block of size `lp.totalSpan`. Every per-elf
  base sits inside it; every safety predicate is bounded by it.
- **Loaded image**: file overlays mmap'd on top of the reservation;
  partial-page BSS zeroed in place; `mprotect`'d to final perms.

## Open work

- **Init-order invariants**: `g.initOrder` indices in bounds and
  duplicate-free.
- **Resolve.Table bounds**: `objectIdx < lm.objects.size` for every
  entry — loop-invariant reasoning over `for ... in lm.objects do`.
- **Bytes preserved / BSS zeroed**: the materialised image agrees
  with file bytes (linksem-style soundness); BSS regions read as 0.
  Both require an abstract `Memory` type + state-monad IO shadow.
- **Init topological order**: `DT_NEEDED` edges respected; cycles
  undefined per gabi 08.

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

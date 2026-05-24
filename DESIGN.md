# LeanLoad Design

LeanLoad is an ELF64 loader whose core stages are Lean data transformations.
Each stage adds data and/or witnesses; later stages consume those witnesses
instead of re-checking the same facts. Native IO is isolated in `Runtime`.

## Pipeline

| Stage        | Kind    | Input → Output | Main responsibility |
| ------------ | ------- | -------------- | ------------------- |
| **Parse**    | monadic | `Runtime.File m → ExceptT String m Parse.Elf` | Decode ELF64 ET_DYN, check load-map/dynamic ranges, attach relocs and call targets to checked segments. |
| **Discover** | monadic | `ObjectFinder m → fuel → path → m Discover.Result` | DFS over `DT_NEEDED`, canonical-name dedup, complete dependency edges, graph-indexed init order, cycle rejection. |
| **Reloc**    | pure    | `Discover.Result → Reloc.Result` | Resolve relocation-referenced symbols and reject referenced unresolved strong symbols. |
| **Layout**   | pure    | `Reloc.Result → Layout.Layout` | Compute base-free per-segment/per-object placement and total span. |
| **Finalize** | pure    | `BoundPlan → Finalize.Result bp` | Emit intrinsic-safe mmap/zero/store/mprotect ops plus witnessed entry/init/fini calls. |
| **Runtime**  | IO      | `LoadOps → IO Unit` | Run trusted syscalls for load ops; Main runs witnessed ctors, builds the startup stack, and jumps. |

The CLI wires these together in `ExceptT String IO`: production `ObjectFinder`
opens/parses the main object, searches dependencies, and hands the resulting
graph/init-order pair to Reloc → Layout → Finalize → Runtime.

## Witness flow

- **Parse** establishes file-range validity, ELF policy, checked PT_LOAD
  segment facts, program-header table mapping for `AT_PHDR`, dynamic-table range
  facts, relocation containment, and executable call targets.
- **Discover** produces a closed `LoadGraph` plus `InitOrder graph`: nonempty
  objects, distinct names, bounded dependency indices, one edge per
  `DT_NEEDED`, and a schedule that puts every dependency before its dependent.
- **Reloc** records the relocation formula selected by `e_machine` and resolves
  only symbols actually referenced by relocation records.
- **Layout** carries page-math and cumulative-span facts needed to place every
  segment inside one reservation.
- **Finalize** turns the plan into a typed `Result`: load ops carry range proofs,
  mmap operations are pairwise disjoint, and entry/init/fini calls carry
  executable-segment witnesses.

## Trust boundary

Verified Lean code has no direct `@[extern]` calls: `Parse/`, `Discover/`,
`Reloc/`, `Layout/`, `Finalize/`, and `Runtime/Basic.lean`.

Trusted code is the runtime edge: `LeanLoad/Runtime.c`,
`Runtime/{File,Memory,Exec}.lean`, `Runtime/Run.lean`, and `Main.lean`.
The current formal boundary is `Finalize.Result`: the finalized `LoadOps` tree
plus user-code transfer witnesses. Syscall semantics and the final process
handoff are trusted by inspection.

## Scope

- **ELF format**: ELF64 ET_DYN only.
- **Architectures**: AArch64 and x86-64 dynamic relocation subsets selected by
  `e_machine`.
- **Parsed data**: selected ELF-header metadata (`e_machine`, program-header
  table location/count), program headers, `PT_DYNAMIC`, dynstr, dynsym sized by
  `DT_HASH.nchain`, RELA/JMPREL, and init/fini arrays.
- **Memory model**: in-process loading. Segments are mapped into leanload's
  address space, then `Runtime.execAndJump` transfers control without
  `execve(2)`.

## Runtime assumptions

The IO load path assumes:

1. The kernel-picked reservation does not overlap existing leanload mappings.
2. No other thread mutates the address space between reservation and jump.
3. No libc locks are held across the trampoline.
4. The loaded binary exits with `exit_group`; thread-scoped `_exit` would leave
   Lean runtime threads alive.
5. Signal handlers are reset to `SIG_DFL` before the jump.

The trampoline constructs an `execve(2)`-style initial stack
(`argc/argv/envp/auxv` plus strings), preserves 16-byte stack alignment, forwards
host auxv values needed by libc, and jumps to the parsed entry point.

## Out of scope

- TLS (`PT_TLS`, TLS relocations, TLSDESC).
- Lazy PLT binding; LeanLoad eagerly resolves relocation records.
- RELR-format relocations.
- `IFUNC` / `STT_GNU_IFUNC`.
- `dlopen` / `dlsym`.
- GNU hash and `.gnu.version_*`.
- A formal syscall or byte-level memory semantics.

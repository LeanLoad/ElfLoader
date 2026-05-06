# LeanLoad Design

Verified ELF loader in Lean 4. The verified core is pure Lean; the
syscall layer sits behind two small `@[extern]` modules.

## Stages

Pipeline (one row per `--debug` section):

| Stage        | Type | Input → Output                                                         |
| ------------ | ---- | ---------------------------------------------------------------------- |
| **Discover** | IO   | path → `LinkMap` (transitive `DT_NEEDED` walk; calls `Parse` per file) |
| **Resolve**  | pure | `LinkMap` → resolution table (undef ref → providing object/symbol)     |
| **Plan**     | pure | `LinkMap` → mmap layout + init/fini order                              |
| **Map**      | IO   | layout → mmap'd regions × kernel-chosen bases                          |
| **Reloc**    | pure | formula × bases × resolution → `Array RelocWrite`                      |
| **Apply**    | IO   | walk the writes; poke bytes into mmap'd memory                         |
| **Init**     | IO   | bases × init order → constructors called                               |
| **Exec**     | IO   | build kernel-style stack, jump to entry; no return                     |

`Parse` (`LeanLoad/Parse/`) is a pure decoder called per file inside
`Discover` — `ByteArray` → `ParsedElf`. It's the only step that reads
raw ELF bytes; every later stage operates on typed records.

Two design rules:

1. **The Layout output is the refinement seam.** `Plan.Layout.Layout`
   (layouts + init/fini order), together with `Reloc.RelocWrite`s
   from the post-bases planner, is what `Map`/`Apply`/`Init`/`Exec`
   consume. Verification targets are stated against it.
2. **Reloc planning straddles `Map`.** Layout and init order are
   computed pre-bases; relocation writes are computed post-bases
   (kernel chooses bases at mmap time). Both are pure (`Layout.lean`,
   `Reloc.lean`); the `load` orchestration threads bases between
   them.

## Trust boundary

- **Verified**: `LeanLoad/Spec/`, `LeanLoad/Parse/`, plus the pure
  top-level modules (`Resolve.lean`, `Layout.lean`, `Reloc.lean`).
  Pure Lean; no `IO`; no imports of `Region`, `Exec`'s extern block,
  or `runtime/`.
- **Trusted**: `runtime/*` (audited C, ~150 lines), the
  `@[extern]` declarations in `LeanLoad/Region.lean` and at the top
  of `LeanLoad/Exec.lean`, plus the IO bodies of `Discover.lean`,
  `Map.lean`, `Exec.lean`, and `Main.lean`.

A grep for `@[extern]` outside `LeanLoad/Region.lean` and
`LeanLoad/Exec.lean` is a smell.

## What's "spec" and what's "impl"

- **Spec**: gabi/abi transcriptions. Every type, constant, and table
  in `LeanLoad/Spec/` cites a specific section of gabi 02–08, the
  AArch64 ELF ABI supplement, etc. The def *is* the spec — there is
  no second copy.
- **Impl**: parsers (`Parse/`), pure pipeline (`Resolve.lean`,
  `Layout.lean`, `Reloc.lean`, `Spec/Reloc/Formula.lean`), IO
  orchestration (`Discover.lean`, `Map.lean`, `Apply.lean`,
  `Exec.lean`, `Main.lean`). These implement gabi's prose-level
  algorithms; we
  prove properties about them in `Thm.lean`.

The split is enforced by which directory things live in. A reader
auditing "what does LeanLoad believe about ELF" reads only `Spec/`.

## Scope

**Architecture: AArch64 and x86-64.** Concrete struct types
(`ElfHeader64`, `Header64` (Phdr), `Rela64`); no 32-bit / typeclass
abstraction layer. The reloc planner is parametric over a per-arch
`Formula` type; per-arch tables live under
`Spec/Reloc/{Aarch64,X86_64}.lean` and `Spec/Reloc/Formula.lean`
dispatches on `e_machine`.

**Parser scope: loader-minimal.** A loader does not need to parse
the full ELF, only what is reachable from program headers and the
dynamic section.

- Parsed: ELF header; program header table; `PT_DYNAMIC` and the
  `.dynamic` array; dynsym + dynstr (size derived from `DT_HASH`'s
  `nchain` or — for gnu-only binaries — from walking the
  `DT_GNU_HASH` chain table); `Rela`/`Rel` and `JMPREL` tables;
  init/fini arrays.
- Skipped: section headers, `.text`/`.bss`/`.rodata` section
  metadata, debug info.

## Naming conventions

- **`Spec/X.lean` ↔ gabi/abi chapter X.** Each Spec file's docstring
  cites its source section.
- **`Parse/X.lean` ↔ `Spec/X.lean`.** Parser bodies in `Parse/`,
  types in `Spec/`. One-to-one filename pairing.
- **Lean module `LeanLoad.Region` ↔ C file `runtime/region.c`.**
- **Extern symbols prefixed `leanload_<topic>_<op>`:**
  `leanload_region_mmap_anon`, `leanload_exec_run`. Flat C namespace,
  so the prefix avoids collisions and aids grep.
- **Opaque Lean types named for what they are** (`Region`), not how
  they are implemented — no `Ptr` suffix.

## CLI

```
leanload <elf>             # load and run; does not return
leanload --debug   <elf>   # same as `load`, with stage-by-stage prints
```

`--debug` runs the full pipeline (mmap, relocate, run ctors, transfer
control) but prints a header and summary per stage so a developer can
see which stage misbehaves if the loaded image crashes. The
dump shows discovered objects, layouts, and init/fini order.

## Debuggability

Three rules that pay off across the project:

1. **`deriving Repr` on every spec/parse/pipeline type.**
   Then `--debug` is structured by construction.
2. **Deterministic output.** No timestamps, no hash-iteration order,
   no addresses chosen by ASLR in the plan. Sort everything that has
   no semantic order — golden tests rely on this.
3. **Structured failure messages.** Errors carry the offending
   relocation type, file offset, symbol name, and computed value —
   not just `panic`.

## Verification

See `verification.md` for the running list of proof obligations and
theorem statements. The audit surface is two files:

- `LeanLoad.Thm` — typed catalogue of every proven theorem.
- `verification.md` — prose context for each obligation.

## Memory ownership

- **Inputs** (ELF files): read via `IO.FS.readBinFile` into a
  `ByteArray`. Small enough that the copy is free, and `Plan`
  reasons over pure data.
- **Outputs** (loaded image): `mmap` regions wrapped as opaque
  `Region` external objects. Mappings live for the process lifetime;
  the kernel reclaims at exit.

## Kernel-style exec

The `Exec` stage builds the same stack `execve(2)` would
(argc/argv/envp/auxv at SP, strings above) and jumps to `e_entry`.
SP is 16-byte aligned (AArch64 ABI + SysV x86-64 § Initial Stack and
Register State). Implementation in `runtime/exec.c`; the trampoline
is per-arch — AArch64 `mov sp, _; br _` and x86-64 `movq _, %rsp;
xor rbp; xor rdx; jmpq *_`. No return: leanload's process *is* the
loaded program after the jump.

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
   process hangs. musl's `_exit` does the right thing; nolibc's
   doesn't (the `examples/static.c` fixture works around this
   manually via `my_syscall1(__NR_exit_group, rc)`).

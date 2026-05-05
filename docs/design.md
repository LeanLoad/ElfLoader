# LeanLoad Design

Verified ELF loader in Lean 4. The verified core is pure Lean; the
syscall layer sits behind two small `@[extern]` modules.

## Stages

Pipeline (input → output; pure unless marked IO):

| Stage        | Type | What it does                                      |
| ------------ | ---- | ------------------------------------------------- |
| **Parse**    | pure | `ByteArray` → `ParsedElf` (single file)           |
| **Discover** | IO   | path → `LinkMap` (transitive `DT_NEEDED` walk)    |
| **Plan**     | pure | `LinkMap` (× bases) → `LoaderPlan` + reloc writes |
| **Load**     | IO   | `LoaderPlan` → live image + transfer of control   |

Three rules:

1. **Stages alternate pure / IO.** The boundary between `Discover`
   and `Plan` is exactly where files become bytes-in-memory; the
   boundary between `Plan` and `Load` is where pure plans become live
   mappings.
2. **The `LoaderPlan` is the refinement seam.** Output of `Plan`,
   input of `Load`. Verification targets are stated against it.
3. **Reloc planning is split across the seam.** Layout/Init/Resolve
   are pure-pre-bases; the actual `RelocWrite`s are pure-post-bases
   (kernel chooses bases at mmap time). Both are in `Plan/`; `Load`
   threads bases between them.

## Module layout

```
LeanLoad.lean              package root (re-exports)
LeanLoad/
  Main.lean                CLI + `load` orchestration
  Test.lean                test exe entry
  Discover.lean            IO walk + LinkMap type
  Region.lean              @[extern] for memory ops (runtime/region.c)
  Map.lean                 mmap'ing + reloc apply (uses Region)
  Run.lean                 @[extern] for control transfer + init/exec
  TestFixture.lean         shared synthObj/synthElf
  Thm.lean                 single audit surface for proven theorems
  Spec/                    gabi/abi transcriptions only
    Header.lean            gabi 02 § ELF Header
    Program.lean           gabi 07 § Program Header
    Dynamic.lean           gabi 08 § Dynamic Section
    StringTable.lean       gabi 04 § String Table
    Symbol.lean            gabi 05 § Symbol Table
    Reloc.lean             gabi 06 § Relocation
    Reloc/Aarch64.lean     aarch64-elf-abi § Dynamic Relocations
    Reloc/X86_64.lean      x86-64-ABI § Relocation Types
  Parse/                   byte decoders (impl)
    Bytes.lean             parser monad
    Header.lean Program.lean Dynamic.lean
    StringTable.lean Symbol.lean Reloc.lean
    File.lean              ParsedElf aggregate + parse
  Plan/                    pure pipeline functions (impl)
    Layout.lean Resolve.lean Init.lean Reloc.lean
    Formula.lean           per-`e_machine` formula dispatch
runtime/                   C shims (unverified)
  region.{h,c}             mmap / mprotect / write
  exec.{h,c}               ctor invocation + transfer of control
  common.h                 shared lean-FFI helpers
docs/
  design.md                this file
  exec.md                  kernel-style stack — argc/argv/envp/auxv
  plan.md                  phased implementation plan
  verification.md          proof obligations + theorem statements
examples/                  C sources for showcase binaries
third_party/               submodules (gabi, musl, …)
```

## Trust boundary

- **Verified**: `LeanLoad/Spec/`, `LeanLoad/Parse/`, `LeanLoad/Plan/`.
  Pure Lean; no `IO`; no imports of `Region`, `Run`'s extern block,
  or `runtime/`.
- **Trusted**: `runtime/*` (audited C, ~150 lines), the
  `@[extern]` declarations in `LeanLoad/Region.lean` and at the top
  of `LeanLoad/Run.lean`, plus the IO bodies of `Discover.lean`,
  `Map.lean`, `Run.lean`, and `Main.lean`.

A grep for `@[extern]` outside `LeanLoad/Region.lean` and
`LeanLoad/Run.lean` is a smell.

## What's "spec" and what's "impl"

- **Spec**: gabi/abi transcriptions. Every type, constant, and table
  in `LeanLoad/Spec/` cites a specific section of gabi 02–08, the
  AArch64 ELF ABI supplement, etc. The def *is* the spec — there is
  no second copy.
- **Impl**: parsers (`Parse/`), pure pipeline functions (`Plan/`),
  IO orchestration (`Discover.lean`, `Map.lean`, `Run.lean`,
  `Main.lean`). These implement gabi's prose-level algorithms; we
  prove properties about them in `Thm.lean`.

The split is enforced by which directory things live in. A reader
auditing "what does LeanLoad believe about ELF" reads only `Spec/`.

## Scope

**Architecture: AArch64 and x86-64.** Concrete struct types
(`ElfHeader64`, `Header64` (Phdr), `Rela64`); no 32-bit / typeclass
abstraction layer. The reloc planner is parametric over a per-arch
`Formula` type; per-arch tables live under
`Spec/Reloc/{Aarch64,X86_64}.lean` and `Plan/Formula.lean` dispatches
on `e_machine`.

**Parser scope: loader-minimal.** A loader does not need to parse
the full ELF, only what is reachable from program headers and the
dynamic section.

- Parsed: ELF header; program header table; `PT_DYNAMIC` and the
  `.dynamic` array; dynsym + dynstr; `Rela`/`Rel` and `JMPREL`
  tables; init/fini arrays.
- Skipped: section headers, `.text`/`.bss`/`.rodata` section
  metadata, debug info, GNU hash, `DT_GNU_HASH`-only binaries.

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
leanload --inspect <elf>   # run Discover + Plan, dump the plan, exit
```

`--inspect` stops before `Map`/`Run`. No `mmap`, no execution. The
dump shows discovered objects, layouts, and init/fini order.

## Debuggability

Three rules that pay off across the project:

1. **`deriving Repr` on every type in `Spec/`, `Parse/`, `Plan/`.**
   Then `--inspect` is structured by construction.
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

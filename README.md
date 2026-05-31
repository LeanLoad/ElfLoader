# ElfLoader [![CI](https://github.com/LeanLoad/ElfLoader/actions/workflows/ci.yml/badge.svg)](https://github.com/LeanLoad/ElfLoader/actions/workflows/ci.yml)

A verified ELF loader in Lean 4 for PIE Linux ELF binaries
(static-PIE + dynamically-linked), targeting AArch64 + x86-64 with
musl libc.

Architecture: an **invariant-carrying Lean middle** — `Parse` → `Discover` →
`Reloc` → `Layout` → `Finalize` — with trusted IO instantiations at the edges:
the CLI's production object finder (open/path-search/read) at the front and
`Runtime.Run` + `execAndJump` (mmap + writes + control transfer) at the back.

See [`run.log`](run.log) for a committed end-to-end debug trace.

## Quick start

Use the LeanLoad umbrella checkout for the full fixture/runtime path:

```sh
git clone --recurse-submodules git@github.com:LeanLoad/LeanLoad.git
cd LeanLoad
./setup.sh               # install system C toolchain, elan, and third_party/impl/musl
make run                 # build elfloader + examples, run on ElfLoader/build/main
```

For package-only work in this repo, `lake build elfloader` does not require
the umbrella third_party checkout. `./run.sh` and `make` expect
`THIRD_PARTY_DIR` to point at the umbrella's `third_party` directory
(`../third_party` when checked out as `LeanLoad/ElfLoader`).

Unit-level invariants live as `#guard` blocks in implementation
and example files (`Discover/Examples.lean`, `Examples.lean`, …) and elaborate during
`lake build`. The integration test is `./run.sh` end-to-end against
`build/main`.

## Audit surface

The byte-level trust surface is [`ElfLoader/Parse/`](ElfLoader/Parse/)
(gABI / psABI C-struct transcriptions and typed views with
gABI-mandated invariants carried as `Segment` fields). The IO trust
seam is [`ElfLoader/Runtime/Run.lean`](ElfLoader/Runtime/Run.lean):
it only interprets the intrinsic-safe `LoadOps` tree inside `Finalize.Result`,
where `SegmentOps`, `ElfOps`, and `LoadOps` fields discharge in-bounds and
pairwise-disjoint without ever materialising a flat predicate array; the same
result also carries entry/init/fini `CallOp` executable-segment witnesses.

See [`DESIGN.md`](DESIGN.md) for the full pipeline + trust-boundary
writeup.

## De facto conventions

ElfLoader follows several conventions that are *not* mandated by gABI
but are universal across glibc / musl / ld.so. We follow them because
real-world programs assume them; deviating would break compatibility.
Where we're *stricter* than the convention (deliberately rejecting
edge cases instead of papering over them), it's called out below.

**Dependency resolution & dedup** (`Discover/`, `ElfLoader/Runtime.c`)

- **Dedup by `DT_SONAME` — required for every NEEDED dependency `.so`.**
  We *fail loud* on a SONAME-less library; ld.so falls back to
  realpath/inode. SONAME is universally set by modern linkers
  (`-Wl,-soname,…`); missing it almost always indicates a build
  mistake. (gABI doesn't mandate dedup at all — see `ld.so(8)`.)
- **Main executable's canonical name = path basename.** Executables
  conventionally don't set SONAME (nothing should link against an
  exe); we use `basename(mainPath)`, never consulting SONAME.
- **Search order for NEEDED lives in Lean (`Discover/Search.lean`).**
  gABI 08 order is: literal path after dynamic-string substitution if
  the name contains `/`; otherwise `DT_RPATH` only when `DT_RUNPATH` is
  absent; then `LD_LIBRARY_PATH`; then `DT_RUNPATH`; then default dirs.
  Runtime C only opens exact candidate paths.
- **Host-specific defaults are explicit policy.** gABI delegates default
  directories to the psABI/system. ElfLoader records a deterministic
  Linux x86-64 oriented list in `Discover.Search.defaultDirs`.
- **RPATH scope is deliberately local.** gABI 08 explicitly scopes
  `DT_RUNPATH` to immediate dependencies but does not state whether the
  deprecated `DT_RPATH` should inherit down an ancestor chain. glibc does
  ancestor-chain RPATH search when no RUNPATH is present; ElfLoader keeps
  each `WorkItem` local to the referring object and uses only that
  object's `DT_RPATH`.
- **Opened-but-rejected candidates do not end search.** gABI requires
  exhausting all paths after wrong ELF header attributes. ElfLoader applies
  the same search-exhaustion behavior to any parse rejection from an
  opened candidate, then reports all parse failures if no candidate
  succeeds.

**Layout & process startup** (`Parse/`, `Layout/`, `Finalize/`, `Main.lean`)

- **PT_LOAD segments pairwise disjoint.** gABI only mandates sorted
  `p_vaddr` order; non-overlap is de facto. We carry it as a
  validated `NonOverlap` witness on `Elf`.
- **Program-header table is file-backed by some PT_LOAD.** Required so
  `AT_PHDR` can be reported as a loaded virtual address. Validated by
  constructing a `ProgramHeaderMap` (see
  [`Parse/LoadMap/ProgramHeader/Map.lean`](ElfLoader/Parse/LoadMap/ProgramHeader/Map.lean))
  that records the covering PT_LOAD and translates `e_phoff` through it
  via `eaddrOfFileOff` — no first-PT_LOAD or `vaddr = offset` assumption.
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

**Init / fini** (`Finalize/Build.lean`)

- **Init order = DFS post-order over the full dependency graph; fini =
  its reverse.** gABI 08 mandates a *partial* order ("deps before
  dependents") and leaves cycle order undefined. For acyclic graphs our
  DFS post-order matches glibc / musl; reverse-init for fini is also
  their choice.
- **Cyclic `DT_NEEDED` graphs are supported with deterministic cycle
  breaks.** gABI 08 does not specify cyclic initializer ordering, so
  active-stack dedup hits are recorded as real graph edges and
  `InitOrder.classifiesDeps` makes the chosen placement explicit:
  normal edges place the dependency before the dependent; self/reverse
  placements are ElfLoader's deterministic DFS cycle breaks.
- **Zero entries in `DT_INIT_ARRAY` / `DT_FINI_ARRAY` skipped as
  no-ops.** gABI leaves them unspecified; glibc / musl skip them.

**Relocations** (`Parse/Reloc/`, `Reloc/`, `Finalize/Reloc.lean`)

- **RELA only, not REL.** Toolchains emit RELA for x86_64 + AArch64;
  REL is legacy.
- **`R_*_GLOB_DAT` addend `A` treated as 0.** psABI documents the
  formula as `S + A` for completeness, but linkers emit GLOB_DAT
  with `A = 0`; a nonzero addend would be a malformed link.
- **Strong undef → fail loud at `Reloc.Result.ofDiscover`.** ld.so
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
- **No TLS yet** (deferred). The fixture's
  `__thread` test works because musl's pthread bootstrap synthesizes
  TLS state at thread-creation time, not via ELF TLS phdrs.

## Where gABI overspecifies

gABI marks several fields "mandatory" — or imposes alignment / ordering
rules — that real loaders don't enforce. The flip side of "De facto
conventions" above: there, gABI is silent where reality has a
convention; here, gABI is strict where reality is lax. ElfLoader's
posture per field is in the bullet.

**`DT_STRSZ` (gABI 08 § Dynamic, "mandatory" for exec + shared)**

- musl's `ldso/dynlink.c` never reads it — `dso->strings` is a bare
  `char*` indexed by `st_name`, trusting NUL termination. glibc reads
  it only in `elf/dl-addr.c` for `dladdr`'s bounds check, not on the
  load path. A `.so` missing `DT_STRSZ` would load fine under both.
- ElfLoader uses it as the pread byte count for `.dynstr`. Absence →
  empty strtab (silent, not an error). The `DT_STRTAB` / `DT_STRSZ`
  pair is resolved to a `FileRange` in
  [`Parse/DynMap/Basic.lean`](ElfLoader/Parse/DynMap/Basic.lean) and
  read by `parseFile` in [`Parse.lean`](ElfLoader/Parse.lean).

**`DT_HASH` (gABI 08, "mandatory")**

- `--hash-style=gnu` (modern default on most distros) emits only
  `DT_GNU_HASH`, omitting `DT_HASH`. glibc + musl walk GNU-hash chains
  in that case; gABI never mentions `DT_GNU_HASH` at all.
- ElfLoader sidesteps by requiring `--hash-style=both` in the Makefile
  so `DT_HASH.nchain` is always available as the symtab count (the
  only section whose size doesn't pair with a `DT_*SZ` tag).

**`DT_RELAENT` / `DT_SYMENT` / `DT_PLTREL` (gABI 08, "mandatory")**

- Entry-size tags. Every loader hardcodes the sizes (24 / 24 / 8)
  because they're fixed by gABI itself — reading them would be
  circular. ElfLoader does the same: `RawRelaSize`, `RawSymSize`,
  `RawDynSize` are compile-time constants; the tags are ignored.

**Section headers (gABI 03)**

- gABI describes section headers extensively, but loaders don't need
  them at all — only `.dynamic` matters at load time. `strip
  --strip-all` removes them; many production binaries ship without.
- ElfLoader strips them too: the fixture sets `e_shoff = 0`, and the
  parser never reads section headers — only the program-header table
  + `.dynamic`.

**`DT_RPATH` "deprecated" (gABI 08)**

- gABI deprecates `DT_RPATH` in favor of `DT_RUNPATH`, but ld.so still
  honors both with quirky precedence rules. So "deprecated in gABI"
  understates how alive it is in practice.
- ElfLoader implements the gABI compatibility rule: `DT_RPATH` is searched
  before `LD_LIBRARY_PATH` only when `DT_RUNPATH` is absent; if both are
  present, only `DT_RUNPATH` participates.
- gABI does not state whether `$ORIGIN` substitution is valid inside
  `DT_RPATH`: the substitution section names `DT_NEEDED` and
  `DT_RUNPATH`, while the RPATH note says only that RPATH is a
  colon-separated search facility. ElfLoader expands `$ORIGIN` in RPATH as
  Linux loaders do; unsupported `$name` forms and malformed `$` sequences
  are rejected because gABI marks them unspecified.

**Dynamic-search policy gaps (gABI 08)**

- **Default directories are host policy.** gABI names `/usr/lib` "or such
  other directories as may be specified by the psABI supplement"; the
  x86-64 psABI names `/lib`, `/usr/lib`, `/lib64`, and `/usr/lib64`;
  Linux multi-arch directories such as `/lib/x86_64-linux-gnu` are distro
  policy. ElfLoader fixes one deterministic Linux x86-64 order in
  `Discover.Search.defaultDirs`.
- **`$ORIGIN` requires a canonical directory but not a mechanism.** gABI
  requires an absolute directory path with no symlinks and no `.`/`..`
  components. ElfLoader gets that witness through the C shim
  `elfloader_canonical_origin_dir`, implemented with `realpath(3)`, and
  stores it on `DiscoveredObject` rather than on `Runtime.File`.
- **Privilege-sensitive search restrictions are out of model.** gABI notes
  that set-user/set-group or otherwise privileged programs ignore
  `LD_LIBRARY_PATH` and restrict `$ORIGIN`. ElfLoader is a userspace loader
  inside an already-running process, not a kernel `execve` privilege
  transition, so it does not model those restrictions.
- **`DF_ORIGIN` is not used as a policy gate.** gABI says an
  implementation may require `DF_ORIGIN` for some `$ORIGIN`-using
  `dlopen()` cases. ElfLoader does not implement `dlopen()` and resolves
  startup `DT_NEEDED` only, so `$ORIGIN` in startup dynamic strings is
  accepted without checking `DF_ORIGIN`.
- **RPATH inheritance is unspecified.** gABI gives immediate-dependency
  scope only for `DT_RUNPATH`; it does not define whether old
  `DT_RPATH` directories apply to descendants. ElfLoader does not inherit
  ancestor RPATHs. If compatibility with glibc's historical chain search
  becomes a goal, this should become an explicit graph/search invariant
  rather than hidden in Runtime.

**`EI_OSABI` / `EI_ABIVERSION` (gABI 02)**

- gABI says these identify the target OS ABI; Linux's loader ignores
  the values in practice.
- ElfLoader parses but doesn't validate against an allowlist.

**`p_align` congruence (gABI 07 § Program Header, "must")**

- gABI says PT_LOAD `p_vaddr` and `p_offset` "must" be congruent both
  modulo the page size and modulo `p_align`. elflint enforces both;
  glibc's `elf/dl-load.c` checks only mod page size (`"ELF load command
  address/offset not page-aligned"`); musl's `ldso/dynlink.c` never
  checks either — it masks `p_offset & -PAGE_SIZE` and mmap's. A binary
  with junk low bits in `p_align` loads fine under both libc's.
- ElfLoader carries a per-segment `alignCong` witness modulo `p_align`
  (gABI-strict — stricter than either loader). See
  [`Parse/LoadMap/Segment/Basic.lean`](ElfLoader/Parse/LoadMap/Segment/Basic.lean).

**`DT_TEXTREL` "deprecated" in favor of `DF_TEXTREL` (gABI 08)**

- gABI 08 marks `DT_TEXTREL` deprecated in favor of `DT_FLAGS |
  DF_TEXTREL`. In practice the deprecated form is the canonical one:
  musl scans only `DT_TEXTREL`, never `DF_TEXTREL`; glibc rewrites
  `DF_TEXTREL` into a synthetic `DT_TEXTREL` at load because that's
  the form its reloc loop checks. The "deprecated" tag never died.
- ElfLoader's per-arch reloc tables don't enumerate any text-touching
  relocs, so we never emit a text-segment write — protection by
  omission, not by safety predicate. (`SegmentOps` checks in-bounds
  and disjointness; it doesn't inspect `PF_W`.)

**`PT_INTERP` uniqueness + position (gABI 07)**

- gABI says a file "may" contain a `PT_INTERP` entry and is silent on
  duplicates or where it sits among the phdrs. elflint enforces "at
  most one" *and* "must precede the first `PT_LOAD`" as hard errors;
  glibc + musl just stop at the first one they see and never re-scan.
- ElfLoader is itself the interpreter — `PT_INTERP` of the main is
  ignored (we don't recursively load an `ld-linux.so`).

## Where gABI underspecifies

The opposite extreme of the previous section: features every modern
binary contains and every modern loader requires, that gABI 07/08
never describes.

**`PT_GNU_STACK` / `PT_GNU_RELRO` / `PT_GNU_EH_FRAME` / `PT_GNU_PROPERTY`**

- gABI 07's `p_type` table goes up to `PT_TLS` and stops. Every modern
  toolchain emits `PT_GNU_STACK` (kernel reads it to decide whether to
  grant an executable stack — *security-critical default*),
  `PT_GNU_RELRO` (ld.so re-mprotects the region read-only after
  relocations), `PT_GNU_EH_FRAME` (libgcc / libunwind require it for
  C++ exceptions and backtraces), and `PT_GNU_PROPERTY` (CET / BTI).
  elflint accepts them as known.
- ElfLoader doesn't yet recognize these phdr types; we mmap PT_LOAD,
  set stack non-exec by construction (separate anon mmap, no
  `PROT_EXEC`), and don't apply RELRO.

**Symbol versioning: `DT_VERSYM` / `DT_VERDEF` / `DT_VERNEED` +
`DT_VERDEFNUM` / `DT_VERNEEDNUM`**

- Not in gABI at all. Every glibc-linked `.so` has `DT_VERSYM`;
  glibc's `dl-lookup.c` filters every symbol resolution by version
  index, and `libc.so.6`'s `GLIBC_2.x` ABI compatibility depends on
  it. No `DT_*SZ` tag pairs with `DT_VERDEF` / `DT_VERNEED` —
  toolchains emit GNU-private `DT_VERDEFNUM` / `DT_VERNEEDNUM` counts
  that gABI couldn't have specified.
- ElfLoader doesn't yet handle versioned symbols (musl is statically
  linked into the fixture, sidestepping it). A glibc-linked target
  would resolve to the wrong symbol version.

**`STT_GNU_IFUNC` / `STB_GNU_UNIQUE`**

- gABI 05's symbol-type / binding tables stop at `STT_TLS` and
  `STB_WEAK`. `STT_GNU_IFUNC` (resolver function called at relocation
  time — how glibc dispatches `memcpy` to AVX vs SSE2) and
  `STB_GNU_UNIQUE` (process-wide single instance, used by libstdc++
  for template static data) live in the OS-specific range. glibc's
  `dl-lookup.c` accepts both.
- ElfLoader's `SymBind` is a closed enum (`local` / `global` / `weak`);
  anything else fails `SymBind.ofRaw`. IFUNC / UNIQUE symbols are
  rejected at elaborate, not silently miscompiled.

**`PN_XNUM` (`e_phnum` overflow escape)**

- gABI 02 describes `e_phnum` as a 16-bit count and never says what to
  do when a binary has ≥ 0xffff phdrs. Binutils + kernel + elflint
  agree on a convention: when `e_phnum == 0xffff`, the actual count
  lives in `section[0].sh_info`. elflint implements it; glibc + musl
  haven't needed to because real binaries don't have that many phdrs.
- ElfLoader treats `e_phnum` as a literal count — a ≥64K-phdr binary
  (none exist in practice for our targets) would silently truncate.

## Module layout

```
ElfLoader.lean              package root (re-exports)
Main.lean                  CLI executable entry — Lake-blessed top-level
ElfLoader/
  Basic.lean               cross-stage scalar wrappers (`ByteSize`, `FileOff`,
                           `Eaddr`) + `require` / `buildFinFunction` helpers
  Parse.lean               public parse entry: checked `Elf`, `parseFile`, `parseByteArray`
  Parse/
    Basic.lean             parse-stage address / range / size wrappers and
                           `DecodableFromScalar` lifts
    Decode/                byte decoder primitives + `Decodable` deriving support
    Strtab.lean            gABI 04 string-table buffer + UTF-8 lookup
    Symbol/                raw `Elf64_Sym`, `DT_HASH` SysV header, checked `Symbol` bundle
    LoadMap/               checked ELF header / ident / phdr table / PT_LOAD map used
                           before any dynamic-virtual-address read
    DynMap/                `.dynamic` table: raw tag list + resolved `DynMap`
                           (string offsets, file ranges, ELF addresses)
    Reloc/                 raw `Elf64_Rela`, segment-located checked `Reloc`,
                           and `RelocTable` grouped by rela / jmprel
    CallTargets.lean       checked `e_entry` + `DT_INIT_ARRAY` / `DT_FINI_ARRAY`
                           targets, each witnessed against an executable PT_LOAD
    Examples.lean          checked parse fixture and cross-section #guards
  Discover.lean            public Discover interface: `DiscoveredObject`, `LoadGraph`,
                           `WorkItem`, monadic `ObjectFinder`
  Discover/
    Names.lean             canonical naming policy: `DT_SONAME` for deps,
                           path basename for main
    Provider.lean          `ObjectFinder m` effect boundary used by traversal
    Search.lean            gABI dependency-search policy: RPATH/RUNPATH/env,
                           `$ORIGIN`, default dirs, exact-open candidates
    Graph.lean             dependency-graph reachability theorems
    Order.lean             init-order predicates and `Nodup` / placement lemmas
    Builder.lean           `Discovered` construction carrier + smart constructors
                           (initial/pushObject/recordDep/markComplete) + characterisation theorems
    Traversal.lean         `ActiveStack`, `WorkResult` / `WorkListAcc`, and the
                           mutual `discoverWork` / `discoverWorkList`
    Finalize.lean          monadic `discover` top-level (promotes final state to LoadGraph)
    Examples.lean          private in-memory ObjectFinder + #guard scenarios
                           (linear/diamond/cycle/SONAME/search-order)
  Reloc.lean               base-free relocation planning over the discovered graph
  Reloc/
    Symbol.lean            single-elf "first global definition" lookup (`MatchedSym`)
    ResolutionOrder.lean   gABI 08 BFS view of the dep graph (`bfsOrder`,
                           nodup, head = main)
    Resolve.lean           across-elves first-match-along-order lookup (`SymRef`)
    ABI.lean               per-arch relocation formulas and write widths
  Layout.lean              public Layout stage: `Layout`, `ofRelocResult`, `assignBases`
  Layout/                  base-free page layout helpers
    Align.lean             alignment / page-math helpers over UInt64
    Segment.lean           per-segment layout (file + bss + mprotect shape)
    Elf.lean               per-object layout tree + page-aligned span
  Finalize.lean            public Finalize interface: `BoundPlan` and intrinsic-safe
                           `LoadOps` tree
  Finalize/                    base-aware stage — turn Reloc + Layout into witnessed ops
    Range.lean             pure half-open `UInt64` interval predicates
                           (`Disjoint`, `InRange`) used by safety witnesses
    BoundPlan.lean         `BoundPlan` accessors and reservation-bound proofs
    Reloc.lean             relocation baking — apply ABI formulas at the bound base
    LoadOps.lean           `setupSegment`, op lemmas, and diagnostic op collectors
    Build.lean             builder: `BoundPlan` → intrinsic-safe `LoadOps` tree;
                           proof-carrying ctor / fini call lists
  Runtime.lean             public Runtime facade
  Runtime/
    File.lean              exact open, file size, and pread capability
    Memory.lean            concrete reserve, mmapFile, zero, store, and mprotect effects
    Exec.lean              constructor calls and final jump
    Run.lean               concrete interpreter for finalized `LoadOps`
  Runtime.c                C shims behind the `@[extern]` declarations
  Examples.lean            cross-stage `#guard` walkthrough (synthetic fixtures)
examples/                  C sources for showcase binaries (PIE main + libfoo/bar/baz)
../third_party/            umbrella submodules (musl, gabi, glibc, elfutils, …)
```

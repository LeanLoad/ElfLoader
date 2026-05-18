# LeanLoad [![CI](https://github.com/ShawnZhong/LeanLoad/actions/workflows/ci.yml/badge.svg)](https://github.com/ShawnZhong/LeanLoad/actions/workflows/ci.yml)

A verified ELF loader in Lean 4 for Linux ELF binaries (static +
dynamically-linked), targeting AArch64 + x86-64 with musl libc.

Architecture: a **pure verified middle** — `Parse` → `Elaborate` →
`Discover` → `Plan` → `Materialize` — bracketed by two **trusted IO
bookends**: `Discover.discover` (file reads) at the front and
`LoadOps.runSafe` + `execAndJump` (mmap + writes + control transfer)
at the back.

https://github.com/ShawnZhong/LeanLoad/blob/4f885ee61cfbb39d6359b42f4086aa4c32116342/run.log#L1-L319

## Quick start

```sh
./setup.sh               # one-shot: install system C toolchain, init submodules
./run.sh                 # build leanload + examples, run on build/main
```

Unit-level invariants live as `#guard` blocks in implementation
files (`Discover/Test.lean`, `Example.lean`, …) and elaborate during
`lake build`. The integration test is `./run.sh` end-to-end against
`build/main`.

## Audit surface

The byte-level trust surface is [`LeanLoad/Parse/`](LeanLoad/Parse/)
(gABI / psABI C-struct transcriptions) and
[`LeanLoad/Elaborate/`](LeanLoad/Elaborate/) (typed views with
gABI-mandated invariants carried as `Segment` fields). The IO trust
seam is `LoadOps.runSafe` in
[`LeanLoad/Materialize/Safety.lean`](LeanLoad/Materialize/Safety.lean):
it only accepts a `LoadSafe`-witnessed `LoadOps` tree, where
`SegmentSafe` / `ElfSafe` / `LoadSafe` together discharge in-bounds
and pairwise-disjoint without ever materialising a flat predicate
array. Soundness theorems against the abstract `Memory` model live
in [`LeanLoad/Spec/`](LeanLoad/Spec/).

See [`DESIGN.md`](DESIGN.md) for the full pipeline + trust-boundary
writeup.

## De facto conventions

LeanLoad follows several conventions that are *not* mandated by gABI
but are universal across glibc / musl / ld.so. We follow them because
real-world programs assume them; deviating would break compatibility.
Where we're *stricter* than the convention (deliberately rejecting
edge cases instead of papering over them), it's called out below.

**Dependency resolution & dedup** (`Discover/`, `LeanLoad/Runtime.c`)

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

**Init / fini** (`Materialize/Build.lean`)

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
- **No TLS yet** (deferred). The fixture's
  `__thread` test works because musl's pthread bootstrap synthesizes
  TLS state at thread-creation time, not via ELF TLS phdrs.

## Where gABI overspecifies

gABI marks several fields "mandatory" — or imposes alignment / ordering
rules — that real loaders don't enforce. The flip side of "De facto
conventions" above: there, gABI is silent where reality has a
convention; here, gABI is strict where reality is lax. LeanLoad's
posture per field is in the bullet.

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

**`p_align` congruence (gABI 07 § Program Header, "must")**

- gABI says PT_LOAD `p_vaddr` and `p_offset` "must" be congruent both
  modulo the page size and modulo `p_align`. elflint enforces both;
  glibc's `elf/dl-load.c` checks only mod page size (`"ELF load command
  address/offset not page-aligned"`); musl's `ldso/dynlink.c` never
  checks either — it masks `p_offset & -PAGE_SIZE` and mmap's. A binary
  with junk low bits in `p_align` loads fine under both libc's.
- LeanLoad carries a per-segment `alignCong` witness modulo `p_align`
  (gABI-strict — stricter than either loader). See
  [`Elaborate/Segment.lean`](LeanLoad/Elaborate/Segment.lean).

**`DT_TEXTREL` "deprecated" in favor of `DF_TEXTREL` (gABI 08)**

- gABI 08 marks `DT_TEXTREL` deprecated in favor of `DT_FLAGS |
  DF_TEXTREL`. In practice the deprecated form is the canonical one:
  musl scans only `DT_TEXTREL`, never `DF_TEXTREL`; glibc rewrites
  `DF_TEXTREL` into a synthetic `DT_TEXTREL` at load because that's
  the form its reloc loop checks. The "deprecated" tag never died.
- LeanLoad's reloc tables don't include any text-touching relocs, and
  PT_LOAD writability is segment-level (`PF_W`), so a text reloc would
  attempt to write into a non-writable region and fail elaboration.

**`PT_INTERP` uniqueness + position (gABI 07)**

- gABI says a file "may" contain a `PT_INTERP` entry and is silent on
  duplicates or where it sits among the phdrs. elflint enforces "at
  most one" *and* "must precede the first `PT_LOAD`" as hard errors;
  glibc + musl just stop at the first one they see and never re-scan.
- LeanLoad is itself the interpreter — `PT_INTERP` of the main is
  ignored (we don't recursively load an `ld-linux.so`).

## Where gABI underspecifies

The previous section caught gABI being strict where reality is lax.
This one catches the opposite extreme: features every modern binary
contains and every modern loader requires, that gABI 07/08 never
describes. (Distinct from "De facto conventions" above, which lists
*our* implementation choices in gABI-silent areas — these are about
toolchain-emitted bytes we have to handle whether we like it or not.)

**`PT_GNU_STACK` / `PT_GNU_RELRO` / `PT_GNU_EH_FRAME` / `PT_GNU_PROPERTY`**

- gABI 07's `p_type` table goes up to `PT_TLS` and stops. Every modern
  toolchain emits `PT_GNU_STACK` (kernel reads it to decide whether to
  grant an executable stack — *security-critical default*),
  `PT_GNU_RELRO` (ld.so re-mprotects the region read-only after
  relocations), `PT_GNU_EH_FRAME` (libgcc / libunwind require it for
  C++ exceptions and backtraces), and `PT_GNU_PROPERTY` (CET / BTI).
  elflint accepts them as known.
- LeanLoad doesn't yet recognize these phdr types; we mmap PT_LOAD,
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
- LeanLoad doesn't yet handle versioned symbols (musl is statically
  linked into the fixture, sidestepping it). A glibc-linked target
  would resolve to the wrong symbol version.

**`STT_GNU_IFUNC` / `STB_GNU_UNIQUE`**

- gABI 05's symbol-type / binding tables stop at `STT_TLS` and
  `STB_WEAK`. `STT_GNU_IFUNC` (resolver function called at relocation
  time — how glibc dispatches `memcpy` to AVX vs SSE2) and
  `STB_GNU_UNIQUE` (process-wide single instance, used by libstdc++
  for template static data) live in the OS-specific range. glibc's
  `dl-lookup.c` accepts both.
- LeanLoad's `SymBind` is a closed enum (`local` / `global` / `weak`);
  anything else fails `SymBind.ofRaw`. IFUNC / UNIQUE symbols are
  rejected at elaborate, not silently miscompiled.

**`PN_XNUM` (`e_phnum` overflow escape)**

- gABI 02 describes `e_phnum` as a 16-bit count and never says what to
  do when a binary has ≥ 0xffff phdrs. Binutils + kernel + elflint
  agree on a convention: when `e_phnum == 0xffff`, the actual count
  lives in `section[0].sh_info`. elflint implements it; glibc + musl
  haven't needed to because real binaries don't have that many phdrs.
- LeanLoad treats `e_phnum` as a literal count — a ≥64K-phdr binary
  (none exist in practice for our targets) would silently truncate.

## Module layout

```
LeanLoad.lean              package root (re-exports)
Main.lean                  CLI executable entry — Lake-blessed top-level
LeanLoad/
  Parse/                   byte decoders — Elf64_* C-struct transcriptions
    Decode.lean            parser monad (cursor + Except, u32le / u64le primitives)
    Deriving.lean          `deriving BytesDecode` handler — auto field-by-field decode
    RawEhdr.lean           Elf64_Ehdr + e_ident prefix (gabi 02)
    RawPhdr.lean           Elf64_Phdr (gabi 07) + PT_LOAD / PT_DYNAMIC constants
    RawDyn.lean            Elf64_Dyn + .dynamic array + DT_* tag-keyed lookups (gabi 08)
    RawSym.lean            Elf64_Sym (gabi 05)
    RawRela.lean           Elf64_Rela with explicit addend (gabi 06)
    RawStrtab.lean         byte-buffer NUL-terminated C strings (gabi 04)
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
  Discover/
    Graph.lean             LoadedObject + LoadGraph with non-emptiness / names-Nodup /
                           deps-shape / deps-bounds witnesses + smart constructors
    Effects.lean           abstract IO leaf (resolveDep + fail), monad-polymorphic;
                           instantiated by IO.lean (production) and Test.lean (pure)
    Driver.lean            DFS recursion + DfsState carrier (objects in pre-order,
                           postOrder in return order); `discoverWith` top-level
    IO.lean                Effects.io (Runtime.openByName → parseFromHandle) +
                           `discover` (production entry; opens main, drives DFS)
    Test.lean              Effects.test (over in-memory TestStore) + discoverPure +
                           #guard scenarios (linear/diamond/cycle/SONAME/search-order)
  Plan/                    base-free pure planning — abstract data only
    Align.lean             alignment / page-math helpers over UInt64
    SegmentLayout.lean     per-segment plan (file + bss + mprotect shape), base-free
    Layout.lean            per-object base assignment; totalSpan; segmentsSorted
    Resolve.lean           SymRef n / Unresolved n / Table n with O(1) HashMap index
    Reloc.lean             per-arch formula → `Patch` list with `coversRela` witness
                           + psABI 32-bit overflow check
    Aggregate.lean         top-level `Aggregate.ofGraph` — strong-undef rejection +
                           per-object bundling
  Materialize/             base-aware staging — turn Plan into a witnessed op tree
    BoundPlan.lean         extends `Plan.Aggregate` with the IO-supplied `Reserve`
                           plus the coherence proof tying them
    Reloc.lean             relocation **baking** — apply formulas at the bound base
    LoadOps.lean           `SegmentOps` / `ElfOps` / `LoadOps` tree over typed slot
                           records (`MmapOp` / `ZeroOp` / `StoreOp` / `MprotectOp`)
    Safety.lean            `SegmentSafe` / `ElfSafe` / `LoadSafe` mirror the tree;
                           `LoadOps.runSafe` is the IO trust seam
    Build.lean             builder: `BoundPlan` → safety-witnessed `LoadOps` tree;
                           DFS post-order ctor / fini address lists
  Spec/                    soundness — pure byte-level memory model
    Memory.lean            abstract byte + perm `Memory` type
    Apply.lean             per-op pure denotation over `Memory`
    ApplyLemmas.lean       reusable lemmas about `Apply`
    File.lean              file-content reads
    FFI.lean               opaque `runSafe_image` axiomatized to match Apply
    Soundness.lean         end-to-end soundness theorems
  Runtime.lean             @[extern] trust seam — FileHandle, mmap (file overlay),
                           mmapAnonAlloc, mprotect, write, zeroout, mmapStack,
                           callCtor, execAndJump
  Runtime.c                C shims behind the @[extern] declarations
  Example.lean             cross-stage `#guard` walkthrough (synthetic fixtures)
examples/                  C sources for showcase binaries (PIE main + libfoo/bar/baz)
third_party/               submodules (musl, gabi, glibc, elfutils, …)
```

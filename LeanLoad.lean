/-
Root of the `LeanLoad` library; re-exports every public module.

Pipeline: `Parse → Discover → Reloc → Layout → Finalize → Runtime`.

Each stage takes the *previous* stage's output and adds either data
or a Prop witness. Once an invariant is witnessed, no downstream
stage re-checks it — the witness travels in the type.

  • Parse — bytes in, checked `Parse.Elf` out. Raw fixed-width records are
    decoded first, then `FileView` establishes ELFCLASS64/ELFDATA2LSB/ET_DYN
    policy and PT_LOAD well-formedness before any dynamic virtual-address
    read. Final checked construction attaches relocs to covering segments,
    resolves dynamic strings, checks phdr coverage, and validates init/fini
    targets.

  • Discover — monadic DFS over `DT_NEEDED` via `ObjectFinder m`;
    production instantiates it with path search/open/parse in `ExceptT String IO`.
    The output type witnesses non-emptiness, name `Nodup`, and init-order coverage.

  • Reloc — pure, base-free relocation planning. Takes `Discover.Result`,
    walks dynamic relocation records, resolves only referenced symbols by
    BFS, rejects referenced unresolved strong symbols, and preserves the
    graph-indexed init order for finalization.

  • Layout — pure, base-free. Takes `Reloc.Result`, produces
    `Layout.Layout`: per-elf `SegmentLayout`s with page math +
    per-segment relocs and the cumulative span (`totalSpan`). Carries
    the no-wrap invariants needed for finalize-time safety proofs
    (`pageEnd_lt`, `fileOverlay_le`, `vaddr_memsz_le`, `zero_end_le`,
    `pageInset_eq_vaddr`).

  • Finalize — base-aware and pure. Takes a `BoundPlan` (= `Reloc.Result` +
    `Layout.Layout` + IO `Reserve` + coherence proof) and emits a `LoadOps` tree of
    typed ops (`Mmap` / `Zero` / `Store` / `Mprotect`). The tree carries
    per-op containment and mmap-disjointness witnesses intrinsically.

  • Runtime — the trust seam. `@[extern]` primitives wrapped in
    typed op records; `Runtime.Run` interprets the intrinsic-safe tree only.

  • Formal boundary — the final structured load ops plus safety witnesses.
    Semantic byte-level memory modelling is intentionally out of scope for
    now; the current formal boundary is "we generate well-formed load
    operations".
 -/
import LeanLoad.Basic
import LeanLoad.Parse
import LeanLoad.Parse.Examples
import LeanLoad.Reloc.ABI

import LeanLoad.Runtime
import LeanLoad.Runtime.File
import LeanLoad.Runtime.Memory
import LeanLoad.Runtime.Exec
import LeanLoad.Runtime.Run

import LeanLoad.Discover
import LeanLoad.Discover.Finalize
import LeanLoad.Discover.Examples  -- pure #guard scenarios; elaborate on build

import LeanLoad.Layout.Align
import LeanLoad.Layout.Segment
import LeanLoad.Layout.Basic
import LeanLoad.Reloc.Symbol
import LeanLoad.Reloc
import LeanLoad.Layout

import LeanLoad.Finalize
import LeanLoad.Finalize.LoadOps
import LeanLoad.Finalize.Reloc
import LeanLoad.Finalize.BoundPlan
import LeanLoad.Finalize.Build

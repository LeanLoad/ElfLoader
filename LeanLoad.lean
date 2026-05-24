/-
Root of the `LeanLoad` library; re-exports every public module.

Pipeline: `Parse → Discover → Reloc → Layout → Exec → Runtime`.

Each stage takes the *previous* stage's output and adds either data
or a Prop witness. Once an invariant is witnessed, no downstream
stage re-checks it — the witness travels in the type.

  • Parse — bytes in, checked `Parse.Elf` out. Raw fixed-width records are
    decoded first, then `FileView` establishes ELFCLASS64/ELFDATA2LSB/ET_DYN
    policy and PT_LOAD well-formedness before any dynamic virtual-address
    read. Final checked construction attaches relocs to covering segments,
    resolves dynamic strings, checks phdr coverage, and validates init/fini
    targets.

  • Discover — `Path → IO LoadGraph`. DFS over `DT_NEEDED`. The
    output type witnesses non-emptiness and name `Nodup`.

  • Reloc — pure, base-free relocation planning. Takes `LoadGraph`,
    walks dynamic relocation records, resolves only referenced symbols by
    BFS, and rejects referenced unresolved strong symbols.

  • Layout — pure, base-free. Takes `Reloc.Result`, produces
    `Layout.Layout`: per-elf `SegmentLayout`s with page math +
    per-segment relocs and the cumulative span (`totalSpan`). Carries
    the no-wrap invariants needed for exec-time safety proofs
    (`pageEnd_lt`, `fileOverlay_le`, `vaddr_memsz_le`, `zero_end_le`,
    `pageInset_eq_vaddr`).

  • Exec — base-aware. Takes a `BoundPlan` (= `Reloc.Result` +
    `Layout.Layout` + IO `Reserve` + coherence proof) and emits a `LoadOps` tree of
    typed ops (`Mmap` / `Zero` / `Store` / `Mprotect`). Gated by
    `LoadSafe rsv.addr rsv.len ops`, a structural witness over
    per-op containment and mmap disjointness.

  • Runtime — the trust seam. `@[extern]` primitives wrapped in
    typed op records; `LoadOps.runSafe` accepts the
    safety-witnessed tree only.

  • Formal boundary — the final structured load ops plus safety witnesses.
    Semantic byte-level memory modelling is intentionally out of scope for
    now; the current formal boundary is "we generate well-formed load
    operations".
 -/
import LeanLoad.Parse
import LeanLoad.Parse.Examples
import LeanLoad.Reloc.ABI

import LeanLoad.Exec.Range
import LeanLoad.Runtime

import LeanLoad.Discover
import LeanLoad.Discover.Runtime
import LeanLoad.Discover.Examples  -- pure #guard scenarios; elaborate on build

import LeanLoad.Layout.Align
import LeanLoad.Layout.Segment
import LeanLoad.Layout.Basic
import LeanLoad.Reloc.Symbol
import LeanLoad.Reloc
import LeanLoad.Layout

import LeanLoad.Exec
import LeanLoad.Exec.LoadOps
import LeanLoad.Exec.Safety
import LeanLoad.Exec.Reloc
import LeanLoad.Exec.BoundPlan
import LeanLoad.Exec.Build

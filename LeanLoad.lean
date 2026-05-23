/-
Root of the `LeanLoad` library; re-exports every public module.

Pipeline: `Parse → Discover → Plan → Materialize → Runtime`.

Each stage takes the *previous* stage's output and adds either data
or a Prop witness. Once an invariant is witnessed, no downstream
stage re-checks it — the witness travels in the type.

  • Parse — bytes in, checked `Parse.Elf` out. Raw fixed-width records are
    decoded first, then `LoadMap` establishes ELFCLASS64/ELFDATA2LSB/ET_DYN
    policy and PT_LOAD well-formedness before any dynamic virtual-address
    read. Final checked construction attaches relocs to covering segments,
    resolves dynamic strings, checks phdr coverage, and validates init/fini
    targets.

  • Discover — `Path → IO LoadGraph`. BFS over `DT_NEEDED`. The
    output type witnesses non-emptiness and name `Nodup`.

  • Plan — pure, base-free. Takes `LoadGraph`, produces:
      · `Resolve.Table` — symbol BFS results (no strong-undef).
      · `Layout` — per-elf `SegmentLayout`s with page math +
        per-segment relocs, plus the cumulative span (`totalSpan`).
        Carries the no-wrap invariants needed for materialize-time
        safety proofs (`pageEnd_lt`, `fileOverlay_le`,
        `vaddr_memsz_le`, `zero_end_le`, `pageInset_eq_vaddr`).
      Init order is already bundled in the `LoadGraph` (computed
      during DFS discovery as `g.initOrder`). All three bundled in
      `Plan.Aggregate`.

  • Materialize — base-aware. Takes a `BoundPlan` (= `Plan` + IO
    `Reserve` + coherence proof) and emits a `LoadOps` tree of
    typed slots (`Mmap` / `Zero` / `Store` / `Mprotect`). Gated by
    `Safe rsv.addr rsv.len lo` — the bundle of `MmapsDisjoint` +
    four `*Contained` predicates over the tree.

  • Runtime — the trust seam. `@[extern]` primitives wrapped in
    typed slot records; `LoadOps.runSafe` accepts the
    safety-witnessed tree only.

  • Spec — pure byte-level model of the loader's memory effect
    (`Memory := UInt64 → UInt8`), per-op denotations mirroring
    each `Op.run`, and one FFI axiom relating `LoadOps.runSafe`'s
    image to `LoadOps.apply fs lo Memory.zero`. The substrate the
    three target soundness theorems (`bytes_preserved`,
    `bss_zeroed`, `relocs_applied`) consume.
 -/
import LeanLoad.Parse
import LeanLoad.ABI.Reloc

import LeanLoad.Runtime

import LeanLoad.Discover.State
import LeanLoad.Discover.Driver
import LeanLoad.Discover.IO
import LeanLoad.Discover.Test  -- pure #guard scenarios; elaborate on build

import LeanLoad.Plan.Align
import LeanLoad.Plan.SegmentLayout
import LeanLoad.Plan.Layout
import LeanLoad.Plan.Resolve
import LeanLoad.Plan.Reloc
import LeanLoad.Plan.Aggregate

import LeanLoad.Materialize.LoadOps
import LeanLoad.Materialize.Safety
import LeanLoad.Materialize.Reloc
import LeanLoad.Materialize.BoundPlan
import LeanLoad.Materialize.Build

import LeanLoad.Materialize.Apply
import LeanLoad.Materialize.ApplyLemmas
import LeanLoad.RuntimeAxiom
import LeanLoad.Soundness

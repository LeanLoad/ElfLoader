/-
Root of the `LeanLoad` library; re-exports every public module.

Pipeline: `Parse → Elaborate → Discover → Plan → Materialize → Runtime`.

Each stage takes the *previous* stage's output and adds either data
or a Prop witness. Once an invariant is witnessed, no downstream
stage re-checks it — the witness travels in the type.

  • Parse — byte decode only. Bytes in, `RawElf` out. No semantic
    checks; malformed bytes are caught at `Elaborate`.

  • Elaborate — `RawElf → Except String Elf`. Per-elf validation:
      · ELFCLASS64, ELFDATA2LSB, ET_DYN, supported `e_machine`.
      · Per-segment gabi-07 invariants (`fileszLeMemsz`,
        `alignPow2`, `alignCong`) + LeanLoad's 48-bit `addrBound`.
      · gabi-07 PT_LOAD pair-wise: `Sorted` + `NonOverlap`.
      · Every dynamic rela's 8-byte write window covered by a
        PT_LOAD (`coversRela`).
      · `phdrCovered` — phdr table mapped by a PT_LOAD with
        `vaddr = offset` (so `AT_PHDR = mainBase + phoff` holds).
      · `initArrInExecSeg` / `finiArrInExecSeg` — every ctor /
        dtor entry lives in an executable PT_LOAD.

  • Discover — `Path → IO ObjectList`. BFS over `DT_NEEDED`. The
    output type witnesses non-emptiness and name `Nodup`.

  • Plan — pure, base-free. Takes `ObjectList`, produces:
      · `Resolve.Table` — symbol BFS results (no strong-undef).
      · `LoadPlan` — per-elf `SegmentPlan`s with page math +
        per-segment relocs, plus the cumulative span (`totalSpan`).
        Carries the no-wrap invariants needed for materialize-time
        safety proofs (`pageEnd_lt`, `fileOverlay_le`,
        `vaddr_memsz_le`, `zero_end_le`, `pageInset_eq_vaddr`).
      · `Init.order` — DFS post-order init sequence (`Fin n` typed).
      All four bundled in `Plan.Plan`.

  • Materialize — base-aware. Takes a `BasedPlan` (= `Plan` + IO
    `Reserve` + coherence proof) and emits a `LoadOps` tree of
    typed slots (`Mmap` / `Zero` / `Store` / `Mprotect`). Gated by
    `Safe rsv.addr rsv.len lo` — the bundle of `MmapsDisjoint` +
    four `*Contained` predicates over the tree.

  • Runtime — the trust seam. `@[extern]` primitives wrapped in
    typed slot records; `LoadOps.runSafe` accepts the
    safety-witnessed tree only.
-/
import LeanLoad.Parse.Structs
import LeanLoad.Parse.Dynamic
import LeanLoad.Parse.RawElf

import LeanLoad.Elaborate.Header
import LeanLoad.Elaborate.Strtab
import LeanLoad.Elaborate.Symbol
import LeanLoad.Elaborate.Segment
import LeanLoad.Elaborate.Reloc
import LeanLoad.Elaborate.Elf

import LeanLoad.Runtime

import LeanLoad.Discover.Plan
import LeanLoad.Discover.IO

import LeanLoad.Plan.Align
import LeanLoad.Plan.Layout
import LeanLoad.Plan.Resolve
import LeanLoad.Plan.Reloc
import LeanLoad.Plan.Init
import LeanLoad.Plan.Aggregate

import LeanLoad.Materialize.LoadOps
import LeanLoad.Materialize.Reloc
import LeanLoad.Materialize.BasedPlan
import LeanLoad.Materialize.Build

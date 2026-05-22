/-
Relocation **planning** — base-free.

Phase 1 of 2 in the relocation pipeline:

  1. **Plan** (this file) — `RawRela → Entry objCount seg`. Resolves the
     symbol reference into a `Target` (three explicit cases:
     `noSymbol`, `weakUnresolved`, `resolved ref`) and bundles it with
     the rela's `type` / `r_offset` / `addend` and the inherited
     `coversRela` witness. *Base-free*: no field knows about an mmap
     base. Result lives on each `SegmentLayout.relocs`.
  2. **Bake** (`Materialize/Reloc.lean`) — `Entry objCount seg + base →
     Option StoreOp`. Computes the absolute place and symbol value once
     a reservation base is chosen, then turns each entry into a
     4-or-8-byte `StoreOp` slot. Used by `Materialize.buildSegment`.

The split exists because the kernel picks the per-elf base (`Reserve.run`)
between phases 1 and 2; phase 1 is pure and runs ahead of any IO.

Key types:
  • `Target objCount` — 3-case inductive replacing the old
    `Option (SymRef objCount)`. Lets `Main.debug` distinguish "no symbol"
    from "weak-unresolved" diagnostically; `Materialize.bakeReloc`
    collapses both unresolved cases via `Target.symRef?`.
  • `Entry objCount seg` — parameterised by the owning `Segment` so
    the `coversRela seg.vaddr seg.memsz r_offset` witness from
    `Segment.rela` / `Segment.jmprel` propagates forward into the
    planned tree. `SegmentSafe.storesInRange` reads this witness
    structurally (via `BoundPlan.segment_storeRange_in_rsv`).

This file owns `Entry` and the per-rela planner (`planOne`).
The per-segment planner is called from `Plan/SegmentLayout.lean`'s
`ofSegment` — each `SegmentLayout` carries its own `relocs` array,
so there's no parallel relocation tree to construct or zip later.
-/

import LeanLoad.Plan.Resolve
import LeanLoad.ABI.Reloc
import LeanLoad.Parse.Elf.Entry
import LeanLoad.Parse.Segment.Checked

namespace LeanLoad.Plan.Reloc

open LeanLoad
open LeanLoad.Parse (Elf RawRela Segment Vaddr coversRela)

-- ============================================================================
-- Entry — one rela's planning result. Base-free.
-- Parameterised by the owning segment so the `coversRela` witness
-- (inherited from `Segment.rela` / `Segment.jmprel`'s subtype) can be
-- preserved through planning. `SegmentSafe.storesInRange` needs
-- `r_offset + 8 ≤ seg.vaddr + seg.memsz` to discharge structurally.
-- ============================================================================

/-- Resolution outcome for one rela's symbol reference. Three
    explicit cases collapse the old `Option (SymRef objCount)` to a richer
    discriminator so `Main.debug` can distinguish "no symbol slot"
    from "weak-undefined" diagnostically, and so `Materialize.bakeReloc`
    pattern-matches without an outer `Option`. All three cases drive
    `S = 0` in the formula except `resolved`. -/
inductive Target (objCount : Nat) where
  /-- `r.sym = 0` (`R_*_NONE` and similar). No symbol referenced. -/
  | noSymbol
  /-- Symbol is undef-weak and BFS returned no provider. gabi 05
      binds `S = 0`. -/
  | weakUnresolved
  /-- Symbol resolved: either locally defined or via `Resolve.Table`. -/
  | resolved (ref : Resolve.SymRef objCount)
  deriving Repr

namespace Target

/-- Extract the resolved provider, if any. Used by the bake step
    where both `noSymbol` and `weakUnresolved` collapse to `S = 0`. -/
def symRef? : Target objCount → Option (Resolve.SymRef objCount)
  | .resolved ref => some ref
  | _             => none

/-- Human-readable tag for diagnostics. -/
def tag : Target objCount → String
  | .noSymbol       => "none"
  | .weakUnresolved => "weak"
  | .resolved _     => "ok"

end Target

/-- One planned relocation, owned by `seg`. `target` discriminates the
    three resolution outcomes (no symbol / weak unresolved / resolved
    provider). `Materialize.bakeReloc` collapses the two unresolved
    cases to `S = 0`. The `covered` witness carries the 8-byte-window
    containment from the parent segment forward into the planned tree. -/
structure Entry (objCount : Nat) (seg : Segment) where
  /-- Per-arch relocation type (`R_*`); the low 32 bits of `r_info`. -/
  type     : UInt32
  /-- Segment-relative byte offset for the patch. The absolute address
      `base + r_offset` is computed at materialize time. -/
  r_offset : Vaddr
  /-- Addend `A` (gabi `r_addend`; bit pattern of a signed sxword). -/
  addend   : UInt64
  /-- Resolution outcome — see `Target`. -/
  target   : Target objCount
  /-- 8-byte write window fits in `[seg.vaddr, seg.vaddr + seg.memsz)`.
      Inherited from the `coversRela` subtype on `Segment.rela` /
      `Segment.jmprel`; preserved through `planOne` so the
      materializer can prove `StoresContained` structurally. -/
  covered  : coversRela seg.vaddr seg.memsz r_offset

-- ============================================================================
-- Symbol target resolution. Base-free.
-- ============================================================================

/-- Resolve which `(objectIdx, symIdx)` provides the symbol value
    `S`. Local-defined symbols stay in the referrer; undef refs hop
    via `Resolve.Table.lookup` (total over undef symbols).

    Two residual branches mark edge cases that are reachable in
    principle but not in well-formed inputs:
      • `symtab[symIdx]? = none` — malformed ELF whose rela's `r.sym`
        index exceeds the dynsym size. Could be ruled out structurally
        by adding `r.sym.toNat < symtab.size` to the `Segment.rela` /
        `jmprel` subtypes; cascade through Segment/SegmentLayout/ElfLayout.
      • `.strongUndef` — `Plan.ofObjects` rejects layout when any
        strong-undef remains, but the *type* of `Resolve.Table` does
        not yet witness "no strongUndef". A `noStrongUndef` field
        threaded through that rejection would let the match drop
        this arm.
    Both fall through to `.weakUnresolved` / `.noSymbol`, driving
    `S = 0` in the formula — semantically correct for these edge
    cases. -/
private def resolveTarget (elfs : Array Elf) (rt : Resolve.Table elfs.size)
    (objectIdx : Fin elfs.size) (symIdx : Nat) :
    Target elfs.size :=
  match elfs[objectIdx].symtab[symIdx]? with
  | none       => .noSymbol             -- malformed: symIdx ≥ symtab.size
  | some entry =>
    if !entry.isUndef then
      .resolved ⟨objectIdx, symIdx⟩
    else
      match rt.lookup objectIdx.val symIdx with
      | .found ref   => .resolved ref
      | .weakUndef   => .weakUnresolved
      | .strongUndef => .weakUnresolved -- Plan.ofObjects rejected; defensive

/-- Plan one rela: resolve target, preserve the `coversRela` witness
    from the parent segment. -/
def planOne (elfs : Array Elf) (rt : Resolve.Table elfs.size)
    (objectIdx : Fin elfs.size) (seg : Segment) (r : RawRela)
    (h_cov : coversRela seg.vaddr seg.memsz r.r_offset) :
    Entry elfs.size seg :=
  let target : Target elfs.size :=
    if r.sym == 0 then .noSymbol
    else resolveTarget elfs rt objectIdx r.sym.toNat
  { type := r.type, r_offset := r.r_offset, addend := r.r_addend, target,
    covered := h_cov }

/-- Plan one segment's relas (then jmprel — both go through the same
    formula at materialize time). Used by `Plan.Layout` when
    constructing each `SegmentLayout`. The `coversRela` witness on each
    `seg.rela` / `seg.jmprel` entry is threaded into the planned
    `Entry`'s `covered` field. -/
def planSegment (elfs : Array Elf) (rt : Resolve.Table elfs.size)
    (objectIdx : Fin elfs.size) (seg : Segment) :
    Array (Entry elfs.size seg) := Id.run do
  let mut acc : Array (Entry elfs.size seg) := #[]
  for entry in seg.rela do
    acc := acc.push (planOne elfs rt objectIdx seg entry.val entry.property)
  for entry in seg.jmprel do
    acc := acc.push (planOne elfs rt objectIdx seg entry.val entry.property)
  return acc

end LeanLoad.Plan.Reloc

/-
Relocation planning — base-free.

Per `RawRela` we resolve the symbol target — local-defined refs
become `(this object, sym)`, undef refs go through `Resolve.Table`,
and `r.sym = 0` becomes `none` — and bundle that with the rela's
`type` / `r_offset` / `r_addend` into a `RelocEntry`. None of these
fields knows about an mmap base; the materializer (in
`Materialize.bakeReloc`) computes the absolute place and the symbol
value once a reservation base is chosen.

This file owns the `RelocEntry` type and per-rela planner
(`planOne`). The per-segment planner lives in `Plan/Layout.lean` —
each `SegmentPlan` carries its own `relocs` array, so there's no
parallel-tree-of-relocs to construct or zip against the layout tree
later. `Materialize.bakeSegmentRelocs` reads `sp.relocs` directly.
-/

import LeanLoad.Plan.Resolve
import LeanLoad.Elaborate.Reloc
import LeanLoad.Elaborate.Elf

namespace LeanLoad.Reloc

open LeanLoad
open LeanLoad.Parse (RawRela)
open LeanLoad.Elaborate (Elf Segment coversRela)

-- ============================================================================
-- RelocEntry — one rela's planning result. Base-free.
-- Parameterised by the owning segment so the `coversRela` witness
-- (inherited from `Segment.rela` / `Segment.jmprel`'s subtype) can be
-- preserved through planning. `Materialize.StoresContained` needs
-- `r_offset + 8 ≤ seg.vaddr + seg.memsz` to discharge structurally.
-- ============================================================================

/-- Resolution outcome for one rela's symbol reference. Three
    explicit cases collapse the old `Option (SymRef n)` to a richer
    discriminator so `Main.debug` can distinguish "no symbol slot"
    from "weak-undefined" diagnostically, and so `Materialize.bakeReloc`
    pattern-matches without an outer `Option`. All three cases drive
    `S = 0` in the formula except `resolved`. -/
inductive RelocTarget (n : Nat) where
  /-- `r.sym = 0` (`R_*_NONE` and similar). No symbol referenced. -/
  | noSymbol
  /-- Symbol is undef-weak and BFS returned no provider. gabi 05
      binds `S = 0`. -/
  | weakUnresolved
  /-- Symbol resolved: either locally defined or via `Resolve.Table`. -/
  | resolved (ref : Resolve.SymRef n)
  deriving Repr

namespace RelocTarget

/-- Extract the resolved provider, if any. Used by the bake step
    where both `noSymbol` and `weakUnresolved` collapse to `S = 0`. -/
def symRef? : RelocTarget n → Option (Resolve.SymRef n)
  | .resolved ref => some ref
  | _             => none

/-- Human-readable tag for diagnostics. -/
def tag : RelocTarget n → String
  | .noSymbol       => "none"
  | .weakUnresolved => "weak"
  | .resolved _     => "ok"

end RelocTarget

/-- One planned relocation, owned by `seg`. `target` discriminates the
    three resolution outcomes (no symbol / weak unresolved / resolved
    provider). `Materialize.bakeReloc` collapses the two unresolved
    cases to `S = 0`. The `covered` witness carries the 8-byte-window
    containment from the parent segment forward into the planned tree. -/
structure RelocEntry (n : Nat) (seg : Segment) where
  /-- Per-arch relocation type (`R_*`); the low 32 bits of `r_info`. -/
  type     : UInt32
  /-- Segment-relative byte offset for the patch. The absolute address
      `base + r_offset` is computed at materialize time. -/
  r_offset : UInt64
  /-- Addend `A` (gabi `r_addend`; bit pattern of a signed sxword). -/
  addend   : UInt64
  /-- Resolution outcome — see `RelocTarget`. -/
  target   : RelocTarget n
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
    via `Resolve.Table` (`.found ref` → resolved; `.weakUndef` →
    weakUnresolved).

    Three branches mark cases that are reachable in principle but not
    in well-formed inputs:
      • `symtab[symIdx]?` returns `none` — only happens with a
        malformed ELF whose rela's `r.sym` index exceeds the dynsym
        size. We'd rule this out structurally by validating every
        rela at elaborate time and adding `r.sym.toNat < symtab.size`
        to the `Segment.rela` / `jmprel` subtypes — a moderate
        cascade through `Segment`/`SegmentPlan`/`ElfPlan` types.
      • `rt.index.get?` returns `none` on an undef sym — only happens
        when an undef symbol has no name (empty / `none`), since
        `buildTable` skips those. We'd rule this out by always-
        inserting in `buildTable` (so the lookup is total on undef
        symbols) and adding a `complete` invariant to `Resolve.Table`
        parameterised on the elf array.
      • `.strongUndef` — `Plan.ofObjects` rejects load when any
        strong-undef remains, but the *type* of `Resolve.Table` does
        not yet witness "no strongUndef". A `noStrongUndef` field
        threaded through that rejection would let `match` exhaust
        cleanly.
    All three fall through to `.weakUnresolved` / `.noSymbol`, which
    drive `S = 0` in the formula — semantically correct for these
    edge cases. -/
private def resolveTarget (elfs : Array Elf) (rt : Resolve.Table elfs.size)
    (objectIdx : Fin elfs.size) (symIdx : Nat) :
    RelocTarget elfs.size :=
  match elfs[objectIdx].symtab[symIdx]? with
  | none       => .noSymbol             -- malformed: symIdx ≥ symtab.size
  | some entry =>
    if !entry.isUndef then
      .resolved ⟨objectIdx, symIdx⟩
    else
      match rt.index.get? (objectIdx.val, symIdx) with
      | some (.found ref)  => .resolved ref
      | some .weakUndef    => .weakUnresolved
      | some .strongUndef  => .weakUnresolved -- Plan.ofObjects rejected; defensive
      | none               => .weakUnresolved -- undef sym had empty/no name

/-- Plan one rela: resolve target, preserve the `coversRela` witness
    from the parent segment. -/
def planOne (elfs : Array Elf) (rt : Resolve.Table elfs.size)
    (objectIdx : Fin elfs.size) (seg : Segment) (r : RawRela)
    (h_cov : coversRela seg.vaddr seg.memsz r.r_offset) :
    RelocEntry elfs.size seg :=
  let target : RelocTarget elfs.size :=
    if r.sym == 0 then .noSymbol
    else resolveTarget elfs rt objectIdx r.sym.toNat
  { type := r.type, r_offset := r.r_offset, addend := r.r_addend, target,
    covered := h_cov }

/-- Plan one segment's relas (then jmprel — both go through the same
    formula at materialize time). Used by `Plan.Layout` when
    constructing each `SegmentPlan`. The `coversRela` witness on each
    `seg.rela` / `seg.jmprel` entry is threaded into the planned
    `RelocEntry`'s `covered` field. -/
def planSegment (elfs : Array Elf) (rt : Resolve.Table elfs.size)
    (objectIdx : Fin elfs.size) (seg : Segment) :
    Array (RelocEntry elfs.size seg) := Id.run do
  let mut acc : Array (RelocEntry elfs.size seg) := #[]
  for entry in seg.rela do
    acc := acc.push (planOne elfs rt objectIdx seg entry.val entry.property)
  for entry in seg.jmprel do
    acc := acc.push (planOne elfs rt objectIdx seg entry.val entry.property)
  return acc

end LeanLoad.Reloc

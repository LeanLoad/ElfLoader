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
open LeanLoad.Elaborate (Elf Segment)

-- ============================================================================
-- RelocEntry — one rela's planning result. Base-free.
-- ============================================================================

/-- One planned relocation. `target` is the resolved provider of the
    symbol value `S`: a local definition resolves to `(this object,
    sym)`; an undef ref resolves through `Resolve.Table`; `r.sym = 0`
    or unresolved-weak yields `none` (formula sees `S = 0`). -/
structure RelocEntry (n : Nat) where
  /-- Per-arch relocation type (`R_*`); the low 32 bits of `r_info`. -/
  type     : UInt32
  /-- Segment-relative byte offset for the patch. The absolute address
      `base + r_offset` is computed at materialize time. -/
  r_offset : UInt64
  /-- Addend `A` (gabi `r_addend`; bit pattern of a signed sxword). -/
  addend   : UInt64
  /-- Resolved symbol provider, or `none` for `R_*_NONE` / unresolved. -/
  target   : Option (Resolve.SymRef n)

-- ============================================================================
-- Symbol target resolution. Base-free.
-- ============================================================================

/-- Resolve which `(objectIdx, symIdx)` provides the symbol value
    `S`. Local-defined symbols stay in the referrer; undef refs hop
    via `Resolve.Table`. Returns `none` when the symbol isn't
    defined (unresolved weak refs leave `S = 0`). -/
private def resolveTarget (elfs : Array Elf) (rt : Resolve.Table elfs.size)
    (objectIdx : Fin elfs.size) (symIdx : Nat) :
    Option (Resolve.SymRef elfs.size) :=
  match elfs[objectIdx].symtab[symIdx]? with
  | none       => none
  | some entry =>
    if !entry.isUndef then
      some ⟨objectIdx, symIdx⟩
    else
      (rt.index.get? (objectIdx.val, symIdx)).bind Resolve.Resolution.target?

/-- Plan one rela: resolve target, capture the rest as-is. -/
def planOne (elfs : Array Elf) (rt : Resolve.Table elfs.size)
    (objectIdx : Fin elfs.size) (r : RawRela) : RelocEntry elfs.size :=
  let target :=
    if r.sym == 0 then none
    else resolveTarget elfs rt objectIdx r.sym.toNat
  { type := r.type, r_offset := r.r_offset, addend := r.r_addend, target }

/-- Plan one segment's relas (then jmprel — both go through the same
    formula at materialize time). Used by `Plan.Layout` when
    constructing each `SegmentPlan`. -/
def planSegment (elfs : Array Elf) (rt : Resolve.Table elfs.size)
    (objectIdx : Fin elfs.size) (seg : Segment) :
    Array (RelocEntry elfs.size) := Id.run do
  let mut acc : Array (RelocEntry elfs.size) := #[]
  for entry in seg.rela do
    acc := acc.push (planOne elfs rt objectIdx entry.val)
  for entry in seg.jmprel do
    acc := acc.push (planOne elfs rt objectIdx entry.val)
  return acc

end LeanLoad.Reloc

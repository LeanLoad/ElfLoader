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

/-- One planned relocation, owned by `seg`. `target` is the resolved
    provider of the symbol value `S`: a local definition resolves to
    `(this object, sym)`; an undef ref resolves through
    `Resolve.Table`; `r.sym = 0` or unresolved-weak yields `none`
    (formula sees `S = 0`). The `covered` witness carries the
    8-byte-window containment from the parent segment forward into
    the planned tree. -/
structure RelocEntry (n : Nat) (seg : Segment) where
  /-- Per-arch relocation type (`R_*`); the low 32 bits of `r_info`. -/
  type     : UInt32
  /-- Segment-relative byte offset for the patch. The absolute address
      `base + r_offset` is computed at materialize time. -/
  r_offset : UInt64
  /-- Addend `A` (gabi `r_addend`; bit pattern of a signed sxword). -/
  addend   : UInt64
  /-- Resolved symbol provider, or `none` for `R_*_NONE` / unresolved. -/
  target   : Option (Resolve.SymRef n)
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

/-- Plan one rela: resolve target, preserve the `coversRela` witness
    from the parent segment. -/
def planOne (elfs : Array Elf) (rt : Resolve.Table elfs.size)
    (objectIdx : Fin elfs.size) (seg : Segment) (r : RawRela)
    (h_cov : coversRela seg.vaddr seg.memsz r.r_offset) :
    RelocEntry elfs.size seg :=
  let target :=
    if r.sym == 0 then none
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

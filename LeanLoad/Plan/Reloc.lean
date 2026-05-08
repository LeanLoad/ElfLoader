/-
Relocation planning — base-free.

Per `RawRela` we resolve the symbol target — local-defined refs
become `(this object, sym)`, undef refs go through `Resolve.Table`,
and `r.sym = 0` becomes `none` — and bundle that with the rela's
`type` / `r_offset` / `r_addend` into a `RelocEntry`. None of these
fields knows about an mmap base; the materializer (in
`Materialize.bakeReloc`) computes the absolute place and the symbol
value once a reservation base is chosen.

Output shape mirrors the plan tree: `LoadRelocs` is per-elf, then
per-segment, then per-rela. Indices are parallel to
`LoadPlan.elfs[i].segments[j]` so the materializer can zip them
without an extra mapping.
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

/-- Per-segment relocation plans, in the order they were emitted
    (rela first, then jmprel — matches per-rela iteration in
    `bakeSegmentRelocs`). -/
abbrev SegmentRelocs (n : Nat) := Array (RelocEntry n)

/-- Per-elf list of `SegmentRelocs`, parallel to
    `ElfPlan.segments`. -/
abbrev ElfRelocs (n : Nat) := Array (SegmentRelocs n)

/-- Top-level relocation plan, parallel to `LoadPlan.elfs`. -/
abbrev LoadRelocs (n : Nat) := Array (ElfRelocs n)

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
      (rt.index.get? (objectIdx.val, symIdx)).bind id

/-- Plan one rela: resolve target, capture the rest as-is. -/
private def planOne (elfs : Array Elf) (rt : Resolve.Table elfs.size)
    (objectIdx : Fin elfs.size) (r : RawRela) : RelocEntry elfs.size :=
  let target :=
    if r.sym == 0 then none
    else resolveTarget elfs rt objectIdx r.sym.toNat
  { type := r.type, r_offset := r.r_offset, addend := r.r_addend, target }

/-- Plan one segment's relas (then jmprel — both go through the same
    formula at materialize time). -/
def planSegment (elfs : Array Elf) (rt : Resolve.Table elfs.size)
    (objectIdx : Fin elfs.size) (seg : Segment) :
    SegmentRelocs elfs.size := Id.run do
  let mut acc : SegmentRelocs elfs.size := #[]
  for entry in seg.rela do
    acc := acc.push (planOne elfs rt objectIdx entry.val)
  for entry in seg.jmprel do
    acc := acc.push (planOne elfs rt objectIdx entry.val)
  return acc

/-- Plan one elf: per-segment list, parallel to `elf.segments`. -/
def planElf (elfs : Array Elf) (rt : Resolve.Table elfs.size)
    (objectIdx : Fin elfs.size) : ElfRelocs elfs.size := Id.run do
  let elf := elfs[objectIdx]
  let mut acc : ElfRelocs elfs.size := #[]
  for seg in elf.segments do
    acc := acc.push (planSegment elfs rt objectIdx seg)
  return acc

/-- Plan every elf's relocations. -/
def planAll (elfs : Array Elf) (rt : Resolve.Table elfs.size) :
    LoadRelocs elfs.size := Id.run do
  let mut acc : LoadRelocs elfs.size := #[]
  for h : i in [:elfs.size] do
    acc := acc.push (planElf elfs rt ⟨i, h.upper⟩)
  return acc

end LeanLoad.Reloc

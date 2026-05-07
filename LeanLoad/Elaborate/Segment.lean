/-
The validated single-segment view: a `PT_LOAD` phdr paired with the
relocations whose write window provably falls inside it.

A `Parse.RawPhdr` becomes an `Elaborate.Segment` only after we verify
`p_type = PT_LOAD` and locate the relocations targeting it. This file
owns the per-segment containment predicate (`containsRela`), the
`PF_*` flag bits, and the bundle struct itself. Multi-segment
well-formedness invariants live in `Elaborate/WellFormed.lean`.

Loader-level views (`vaddr`, `length`, `prot`, `endAddr`, …) — which
page-align addresses for `mmap(2)` and translate `PF_*` to POSIX
`PROT_*` — live in `LeanLoad.Plan.Layout`. Those are decisions the
loader makes, not properties the spec dictates.
-/

import LeanLoad.Parse.Structs

-- ============================================================================
-- Per-rela containment predicate. Defined in `Parse.RawPhdr`'s own
-- namespace so dot notation (`phdr.containsRela r`) resolves; the
-- predicate is morally an Elaborate concept (semantic check on raw
-- bytes), but Lean's dot resolution lives by the type's home namespace.
-- ============================================================================

namespace LeanLoad.Parse.RawPhdr

open LeanLoad.Parse (RawPhdr RawRela)

/-- The phdr's memory range fully contains the rela's 8-byte write
    window. Conservatively reserves 8 bytes (the maximum dynamic
    relocation width); 4-byte relocs trivially fit too. The witness
    `phdr.containsRela r` is the bound carried inside
    `Elaborate.Segment`'s rela arrays — established by `elaborate` at
    the parse boundary, consumed downstream for region-bounds-by-
    construction. -/
def containsRela (p : RawPhdr) (r : RawRela) : Prop :=
  p.p_vaddr.toNat ≤ r.r_offset.toNat ∧
  r.r_offset.toNat + 8 ≤ p.p_vaddr.toNat + p.p_memsz.toNat

instance (p : RawPhdr) (r : RawRela) : Decidable (p.containsRela r) := by
  unfold containsRela; infer_instance

end LeanLoad.Parse.RawPhdr

namespace LeanLoad.Elaborate

open LeanLoad.Parse (RawPhdr RawRela)

-- p_flags (gabi 07 Table: Segment Flag Bits)
def PF_X : UInt32 := 0x1
def PF_W : UInt32 := 0x2
def PF_R : UInt32 := 0x4

-- ============================================================================
-- The validated per-segment bundle: a PT_LOAD phdr + its located
-- dynamic relocations. Built by `Elaborate.elaborate`.
-- ============================================================================

/-- A loadable segment plus its located relocations. -/
structure Segment where
  /-- The underlying phdr. The `isLoad` field below is its PT_LOAD
      witness. -/
  phdr   : RawPhdr
  isLoad : phdr.p_type = Parse.PT_LOAD
  /-- General `Rela` relocations (from `DT_RELA`) that target this
      segment. The subtype witness binds each rela's write window
      inside `phdr`'s memory range. -/
  rela   : Array { r : RawRela // phdr.containsRela r }
  /-- PLT relocations (from `DT_JMPREL`) that target this segment. -/
  jmprel : Array { r : RawRela // phdr.containsRela r }

end LeanLoad.Elaborate

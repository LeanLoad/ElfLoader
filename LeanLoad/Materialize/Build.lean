/-
Builder: turn a `BasedPlan` into a safety-witnessed `LoadOps` tree
ready for `runSafe`.

Two top-level entry points:
  • `build`     — pure: `BasedPlan → safety-witnessed LoadOps`.
                  Returns a witnessed
                  `{ lo : LoadOps bp.n // …5 safety predicates… }`. The
                  five `MmapsDisjoint` / `*Contained` predicates are
                  established at construction time via an internal
                  decidable check; a future pass replaces that check
                  with a structural proof rooted in
                  `BasedPlan.base_plus_advance_le_rsv_end` and the
                  per-segment bounds in `Plan/Layout.lean`
                  (`ofSegmentCore_pageVaddr_add_fileOverlayLen_le_pageEndAddr`,
                  `pageEndAddr_le_advance`, …).
  • `ctorAddrs` — pure: `BasedPlan → Array UInt64`. Resolves each
                  init-array entry through the per-elf base, in DFS
                  post-order; ET_DYN entries get the chosen base
                  added, ET_EXEC entries are absolute, zero entries
                  are skipped.

`Main.realize` consumes `build`'s witnessed result via
`LoadOps.runSafe`. There is no separate `safe` entry point.
-/

import LeanLoad.Materialize.LoadOps
import LeanLoad.Materialize.Reloc
import LeanLoad.Materialize.BasedPlan

namespace LeanLoad.Materialize

open LeanLoad
open LeanLoad.Plan (LoadPlan ElfPlan SegmentPlan)
open LeanLoad.Elaborate (Elf Formula)

-- ============================================================================
-- Builder: BasedPlan → LoadOps tree.
-- ============================================================================

/-- Internal: assemble the unwitnessed `LoadOps bp.n` tree from a
    `BasedPlan`. Used by `build`, which then runs the safety
    predicates over the result. -/
private def buildCore (bp : BasedPlan) :
    Except String (LoadOps bp.n) := do
  let plan := bp.plan
  let lp := plan.load
  let elfs := plan.objectElfs
  let formula := plan.formula
  let n := bp.n
  have h_elfs    : elfs.size    = n := plan.objectElfs_size
  have h_lp_elfs : lp.elfs.size = n := lp.elfs_size
  let bases := bp.bases
  have h_bases_n : bases.size = n := bp.bases_size
  have h_bases : bases.size = elfs.size := h_bases_n.trans h_elfs.symm
  have h_n_eq : n = elfs.size := h_elfs.symm
  let mut lo : Array (ElfOps n) := #[]
  for h : i in [:lp.elfs.size] do
    let ep := lp.elfs[i]
    have hi_n : i < n := by rw [← h_lp_elfs]; exact h.upper
    let handle := (plan.objects.val[i]'hi_n).handle
    let base := bases[i]'(by rw [h_bases_n]; exact hi_n)
    let mut segments : Array (SegmentOps n) := #[]
    for h2 : segI in [:ep.segments.size] do
      let sp := ep.segments[segI]
      let (mmap, zero, mprotect) := setupSlots sp handle base
      -- `sp.relocs : Array (RelocEntry n sp.segment)`; bakeSegmentRelocs
      -- wants `Array (RelocEntry elfs.size sp.segment)`. Rewriting
      -- along `n = elfs.size` preserves the segment parameter.
      let relocs : Array (Reloc.RelocEntry elfs.size sp.segment) :=
        h_n_eq ▸ sp.relocs
      let stores ←
        bakeSegmentRelocs formula elfs bases h_bases base sp.segment relocs
      segments := segments.push
        { plan := sp, mmap, zero, stores, mprotect }
    lo := lo.push { base, segments }
  return lo

/-- Witnessed build: assemble the `LoadOps` tree and gate it through
    the five decidable safety predicates
    (`MmapsDisjoint` / `*Contained`) parameterised on the reservation
    `[bp.rsv.addr, +bp.rsv.len)`.

    Returns the witnessed tree on success. Failure means a planner
    bug (the OS would otherwise raise SIGSEGV / mmap failure); the
    body of the proof discharge is residual — see file docstring.

    Callers consume the result via `LoadOps.runSafe`. -/
def build (bp : BasedPlan) :
    Except String { lo : LoadOps bp.n // Safe bp.rsv.addr bp.rsv.len lo } := do
  let lo ← buildCore bp
  if h : Safe bp.rsv.addr bp.rsv.len lo then
    .ok ⟨lo, h⟩
  else
    .error "Materialize.build: planned ops violate safety invariants \
      (loader bug — mmaps collide or extend outside the reservation)"

-- ============================================================================
-- Init address resolution: ctor entries → flat absolute addresses.
-- ============================================================================

/-- Constructor function addresses to call, in init order. Walks
    `order` forward (init); fini callers reverse the result.

    For each elf, walks `elf.initArr`: ET_DYN entries are relative
    (add base); ET_EXEC are absolute. Zero entries are skipped — gabi
    leaves them unspecified, but historical practice (and the table
    layout where zero-terminators are common) treats them as no-ops.

    `order : Array (Fin n)` carries the bound at the type level; both
    `lp.elfs[…]` and `bases[…]` are total — no `[]?` needed. -/
def initAddrs (lp : LoadPlan n) (bases : Array UInt64)
    (h_bases : bases.size = n) (order : Array (Fin n)) : Array UInt64 :=
  Id.run do
    let mut addrs : Array UInt64 := #[]
    for objectIdx in order do
      let ep   := lp.elfs[objectIdx.val]'(by rw [lp.elfs_size]; exact objectIdx.isLt)
      let base := bases[objectIdx.val]'(by rw [h_bases]; exact objectIdx.isLt)
      let isExec := ep.elf.elfType == .exec
      for entry in ep.elf.initArr do
        let fnAddr := if isExec then entry else base + entry
        if fnAddr != 0 then addrs := addrs.push fnAddr
    return addrs

/-- One-shot ctor address resolution from a `BasedPlan`. -/
def ctorAddrs (bp : BasedPlan) : Array UInt64 :=
  initAddrs bp.plan.load bp.bases bp.bases_size bp.plan.initOrder

end LeanLoad.Materialize

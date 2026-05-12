/-
Builder: turn the pure-pipeline `Plan` aggregate into a
safety-witnessed `LoadOps` tree ready for `runSafe`.

Two top-level entry points:
  • `build`     — pure: `(plan, rsv, h_total) → safety-witnessed
                  LoadOps`. Takes the `Plan` aggregate, the IO-side
                  `Reserve`, and a coherence proof
                  `rsv.len = plan.load.totalSpan` (typically threaded
                  off `Reserve.run`'s subtype). Returns a witnessed
                  `{ lo : LoadOps n // …5 safety predicates… }`. The
                  five `MmapsDisjoint` / `*Contained` predicates are
                  established at construction time via an internal
                  decidable check; a future pass replaces that check
                  with a structural proof (the lemma library in
                  `Plan/Layout.lean` covers per-segment `pageEndAddr`
                  bounds, `assignBases_at_toNat`, `cumOffset_mono`,
                  `totalSpan_eq` — the remaining gluing across slot
                  kinds + tree levels is ~200-300 lines but
                  mechanical).
  • `ctorAddrs` — pure: `(plan, rsv) → Array UInt64`. Resolves each
                  init-array entry through the per-elf base, in DFS
                  post-order; ET_DYN entries get the chosen base
                  added, ET_EXEC entries are absolute, zero entries
                  are skipped.

`Main.realize` consumes `build`'s witnessed result via
`LoadOps.runSafe`. There is no separate `safe` entry point.
-/

import LeanLoad.Materialize.LoadOps
import LeanLoad.Materialize.Reloc
import LeanLoad.Plan.Aggregate

namespace LeanLoad.Materialize

open LeanLoad
open LeanLoad.Plan (LoadPlan ElfPlan SegmentPlan)
open LeanLoad.Elaborate (Elf Formula)

-- ============================================================================
-- Builder: Reserve + LoadPlan + handles + formula → LoadOps tree.
-- ============================================================================

/-- Internal: assemble the unwitnessed `LoadOps n` tree from `plan`
    and `rsv`. Used by `build`, which then runs the safety predicates
    over the result. -/
private def buildCore (plan : Plan.Plan) (rsv : Reserve) :
    Except String (LoadOps plan.objects.val.size) := do
  let lp := plan.load
  let elfs := plan.objectElfs
  let handles := plan.objectHandles
  let formula := plan.formula
  let n := plan.objects.val.size
  have h_elfs    : elfs.size    = n := plan.objectElfs_size
  have h_handles : handles.size = n := plan.objectHandles_size
  have h_lp_elfs : lp.elfs.size = n := lp.elfs_size
  let bases := Plan.assignBases rsv.addr lp
  have h_bases_n : bases.size = n :=
    (Plan.assignBases_size rsv.addr lp).trans h_lp_elfs
  have h_bases : bases.size = elfs.size := h_bases_n.trans h_elfs.symm
  have h_n_eq : n = elfs.size := h_elfs.symm
  let mut lo : Array (ElfOps n) := #[]
  for h : i in [:lp.elfs.size] do
    let ep := lp.elfs[i]
    let handle := handles[i]'(by rw [h_handles, ← h_lp_elfs]; exact h.upper)
    let base := bases[i]'(by rw [h_bases_n, ← h_lp_elfs]; exact h.upper)
    let mut segments : Array (SegmentOps n) := #[]
    for h2 : segI in [:ep.segments.size] do
      let sp := ep.segments[segI]
      let (mmap, zero, mprotect) := setupSlots sp handle base
      -- `sp.relocs : Array (RelocEntry n)`; bakeSegmentRelocs wants
      -- `Array (RelocEntry elfs.size)`. Rewriting along `n = elfs.size`.
      let relocs : Array (Reloc.RelocEntry elfs.size) := h_n_eq ▸ sp.relocs
      let stores ← bakeSegmentRelocs formula elfs bases h_bases base relocs
      segments := segments.push
        { plan := sp, mmap, zero, stores, mprotect }
    lo := lo.push { base, segments }
  return lo

/-- Witnessed build: assemble the `LoadOps` tree and gate it through
    the five decidable safety predicates
    (`MmapsDisjoint` / `*Contained`) parameterised on the reservation
    `[rsv.addr, +rsv.len)`. The `h_total : rsv.len = plan.load.totalSpan`
    precondition is the missing fact that `Materialize.safe` used to
    re-check at runtime — threading it from `Reserve.run`'s subtype
    means we can connect the reservation size to `LoadPlan.totalSpan`
    structurally.

    Returns the witnessed tree on success. Failure means a planner
    bug (the OS would otherwise raise SIGSEGV / mmap failure); the
    body of the proof discharge is residual — see file docstring.

    Callers consume the result via `LoadOps.runSafe`. -/
def build (plan : Plan.Plan) (rsv : Reserve)
    (_h_total : rsv.len = plan.load.totalSpan) :
    Except String { lo : LoadOps plan.objects.val.size //
      MmapsDisjoint lo ∧
      MmapsContained rsv.addr rsv.len lo ∧
      ZerosContained rsv.addr rsv.len lo ∧
      StoresContained rsv.addr rsv.len lo ∧
      MprotectsContained rsv.addr rsv.len lo } := do
  let lo ← buildCore plan rsv
  if h : MmapsDisjoint lo ∧
         MmapsContained rsv.addr rsv.len lo ∧
         ZerosContained rsv.addr rsv.len lo ∧
         StoresContained rsv.addr rsv.len lo ∧
         MprotectsContained rsv.addr rsv.len lo then
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

/-- One-shot ctor address resolution from a `Plan` + reservation
    base. The two derived arrays (`bases`, `initOrder`) are typed at
    the same `objects.val.size`, so no coherence proofs leak into the
    caller. -/
def ctorAddrs (plan : Plan.Plan) (rsv : Reserve) : Array UInt64 :=
  let lp := plan.load
  let bases := Plan.assignBases rsv.addr lp
  have h_bases : bases.size = plan.objects.val.size :=
    (Plan.assignBases_size _ _).trans lp.elfs_size
  initAddrs lp bases h_bases plan.initOrder

end LeanLoad.Materialize

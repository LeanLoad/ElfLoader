/-
Builder + safety gate: turn base-free `Plan/` outputs into a
structured `LoadOps` tree, then witness it for `runSafe`.

Three top-level entry points:
  • `build`     — pure: `(rsv, lp, elfs, handles, formula) →
                  LoadOps n`. Takes the typed `Reserve` (with its
                  no-wrap proof) and the matching `LoadPlan n` (with
                  parametric `n` = elf count and `totalSpan_eq`
                  coherence). Computes `bases := Plan.assignBases
                  rsv.addr lp` internally. Per segment: `setupSlots`
                  (mmap, zero, mprotect from the `SegmentPlan` + base)
                  + `bakeSegmentRelocs` (stores from `sp.relocs`).
  • `initAddrs` — pure: `(lp, bases, order) → Array UInt64`. Walks
                  each elf's `initArr` in init order; ET_DYN entries
                  get the chosen base added, ET_EXEC entries are
                  absolute, zero entries are skipped.
  • `safe`      — pure: `(rsv, lo) → safety-witnessed LoadOps`. Runs
                  the decidable safety predicates over the
                  reservation; on success the witness is fed to
                  `LoadOps.runSafe`. Failure means a planner bug —
                  Phase 1 (in progress) replaces this with a static
                  proof so the runtime check goes away.

`Main.realize` uses `safe` then `LoadOps.runSafe`. `Main.load` uses
`build` and `initAddrs`.
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

/-- Build the `LoadOps n` tree from a `Reserve` (with no-wrap
    witness) and a fully populated `Plan` aggregate. The `Plan`
    bundles the `LoadPlan`, the per-elf `Elf`s, the file handles, and
    the per-arch reloc formula at one parametric size, so this
    function has no parallel-array bookkeeping at the call site.

    Computes `bases` internally via `Plan.assignBases rsv.addr
    plan.load`. -/
def build (plan : Plan.Plan) (rsv : Reserve) :
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

-- ============================================================================
-- Safety gate: decidable check over the structured tree.
--
-- Phase 1 replaces this with a static proof on `build`'s output.
-- ============================================================================

/-- Gate the `LoadOps` tree through the decidable safety predicates
    (`MmapsDisjoint`, `MmapsContained`, `ZerosContained`,
    `StoresContained`, `MprotectsContained`) parameterized on the
    reservation `[rsvAddr, rsvAddr+rsvLen)`. Failure means a planner
    bug (the OS would otherwise raise SIGSEGV / mmap failure). -/
def safe (rsv : Reserve) (lo : LoadOps n) :
    Except String { lo : LoadOps n //
      MmapsDisjoint lo ∧
      MmapsContained rsv.addr rsv.len lo ∧
      ZerosContained rsv.addr rsv.len lo ∧
      StoresContained rsv.addr rsv.len lo ∧
      MprotectsContained rsv.addr rsv.len lo } :=
  if h : MmapsDisjoint lo ∧
         MmapsContained rsv.addr rsv.len lo ∧
         ZerosContained rsv.addr rsv.len lo ∧
         StoresContained rsv.addr rsv.len lo ∧
         MprotectsContained rsv.addr rsv.len lo then
    .ok ⟨lo, h⟩
  else
    .error "Materialize.safe: planned ops violate safety invariants \
      (loader bug — mmaps collide or extend outside the reservation)"

end LeanLoad.Materialize

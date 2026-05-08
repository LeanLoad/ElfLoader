/-
Builder + safety gate: turn base-free `Plan/` outputs into a
structured `LoadOps` tree, then witness it for `runSafe`.

Three top-level entry points:
  • `build`     — pure: `(rsv, lp, handles, formula, relocPlan) →
                  LoadOps`. Takes the typed `Reserve` (with its no-wrap
                  proof) and the matching `LoadPlan` (with `lp.totalSpan
                  = rsv.len` coherence proof). Computes `bases :=
                  Plan.assignBases rsv.addr lp` internally. Per
                  segment: `setupSlots` (mmap, zero, mprotect from the
                  `SegmentPlan` + base) + `bakeSegmentRelocs` (stores
                  from the base-free `RelocEntry`s).
  • `initAddrs` — pure: `(lp, bases, order) → Array UInt64`. Walks
                  each elf's `initArr` in init order; ET_DYN entries
                  get the chosen base added, ET_EXEC entries are
                  absolute, zero entries are skipped.
  • `safe`      — pure: `(rsv, lo) → safety-witnessed LoadOps`. Runs
                  the decidable safety predicates over the
                  reservation; on success the witness is fed to
                  `LoadOps.runSafe`. Failure means a planner bug — the
                  proof effort that would make this total is sketched
                  out in the docstring (the lemma library is in place
                  but the per-predicate gluing is not).

`Main.realize` uses `safe` then `LoadOps.runSafe`. `Main.load` uses
`build` and `initAddrs`.
-/

import LeanLoad.Materialize.LoadOps
import LeanLoad.Materialize.Reloc

namespace LeanLoad.Materialize

open LeanLoad
open LeanLoad.Plan (LoadPlan ElfPlan SegmentPlan)
open LeanLoad.Reloc (LoadRelocs)
open LeanLoad.Elaborate (Elf Formula)

-- ============================================================================
-- Builder: Reserve + LoadPlan + relocs → LoadOps tree.
-- ============================================================================

/-- Build the `LoadOps` tree from a `Reserve` (with no-wrap witness),
    a `LoadPlan` (with `totalSpan_eq`), file handles, the per-arch
    reloc formula, and the base-free `LoadRelocs`. Computes `bases`
    internally via `Plan.assignBases rsv.addr lp`.

    The `h_total` coherence proof says `rsv.len = lp.totalSpan` — i.e.,
    the reservation was sized for this exact plan. Together with
    `rsv.noWrap` and `lp.totalSpan_eq`, the safety proofs (deferred
    to Phase 5) can show every emitted slot fits inside the
    reservation. -/
def build (rsv : Reserve) (lp : LoadPlan)
    (elfs : Array Elf) (h_elfs : elfs.size = lp.elfs.size)
    (handles : Array Runtime.FileHandle)
    (h_handles : handles.size = elfs.size)
    (formula : Formula) (relocPlan : LoadRelocs elfs.size) :
    Except String LoadOps := do
  let bases := Plan.assignBases rsv.addr lp
  have h_bases : bases.size = elfs.size :=
    (Plan.assignBases_size rsv.addr lp).trans h_elfs.symm
  let mut lo : Array ElfOps := #[]
  for h : i in [:elfs.size] do
    have hi_lp : i < lp.elfs.size := h_elfs ▸ h.upper
    let ep := lp.elfs[i]'hi_lp
    let handle := handles[i]'(by rw [h_handles]; exact h.upper)
    let base := bases[i]'(by rw [h_bases]; exact h.upper)
    let elfRelocs := (relocPlan[i]?).getD #[]
    let mut segments : Array SegmentOps := #[]
    for h2 : segI in [:ep.segments.size] do
      let sp := ep.segments[segI]
      let (mmap, zero, mprotect) := setupSlots sp handle base
      let segRelocs := (elfRelocs[segI]?).getD #[]
      let stores ← bakeSegmentRelocs formula elfs bases h_bases base segRelocs
      segments := segments.push
        { plan := sp, mmap, zero, stores, mprotect }
    lo := lo.push { base, segments }
  return lo

-- ============================================================================
-- Init address resolution: ctor entries → flat absolute addresses.
-- ============================================================================

/-- Constructor function addresses to call, in init order. Walks
    `order` forward (init); fini callers walk `(initAddrs lp bases
    order).reverse`.

    For each elf, walks `elf.initArr`: ET_DYN entries are relative
    (add base); ET_EXEC are absolute. Zero entries are skipped — gabi
    leaves them unspecified, but historical practice (and the table
    layout where zero-terminators are common) treats them as no-ops. -/
def initAddrs (lp : LoadPlan) (bases : Array UInt64)
    (order : Array Nat) : Array UInt64 := Id.run do
  let mut addrs : Array UInt64 := #[]
  for objectIdx in order do
    let some ep   := lp.elfs[objectIdx]?  | continue
    let some base := bases[objectIdx]?    | continue
    let isExec := ep.elf.elfType == .exec
    for entry in ep.elf.initArr do
      let fnAddr := if isExec then entry else base + entry
      if fnAddr != 0 then addrs := addrs.push fnAddr
  return addrs

-- ============================================================================
-- Safety gate: decidable check over the structured tree.
--
-- The `.error` branch is unreachable when `build` is fed coherent
-- inputs. Making `safe` total requires proving the 5 predicates
-- (`MmapsDisjoint`, `MmapsContained`, `ZerosContained`,
-- `StoresContained`, `MprotectsContained`) about `build`'s output.
-- The lemma library that supports those proofs is in
-- `Plan/Layout.lean` (Phase 1: per-segment `pageEndAddr` bounds;
-- Phase 2: `assignBases_at_toNat` + `cumOffset_mono` + `totalSpan_eq`;
-- Phase 3: `pageEndAddr_le_advance` proof field on `ElfPlan`).
-- The remaining gluing across slot kinds + tree levels (Phase 5) is
-- straightforward but bulky (~200-300 lines). Until then we keep the
-- runtime check; it's O(n) in the number of slots and has never
-- failed in practice.
-- ============================================================================

/-- Gate the `LoadOps` tree through the decidable safety predicates
    (`MmapsDisjoint`, `MmapsContained`, `ZerosContained`,
    `StoresContained`, `MprotectsContained`) parameterized on the
    reservation `[rsvAddr, rsvAddr+rsvLen)`. Failure means a planner
    bug (the OS would otherwise raise SIGSEGV / mmap failure). -/
def safe (rsv : Reserve) (lo : LoadOps) :
    Except String { lo : LoadOps //
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

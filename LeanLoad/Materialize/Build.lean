/-
Builder + safety gate: turn base-free `Plan/` outputs into a
structured `LoadOps` tree, then witness it for `runSafe`.

Three top-level entry points:
  • `build`     — pure: `(lp, handles, bases, formula, relocPlan)
                  → LoadOps`. Per segment: `setupSlots` (mmap, zero,
                  mprotect from the `SegmentPlan` + base) +
                  `bakeSegmentRelocs` (stores from the base-free
                  `RelocEntry`s).
  • `initAddrs` — pure: `(lp, bases, order) → Array UInt64`. Walks
                  each elf's `initArr` in init order; ET_DYN entries
                  get the chosen base added, ET_EXEC entries are
                  absolute, zero entries are skipped.
  • `safe`      — pure: `(rsvAddr, rsvLen, lo) → safety-witnessed
                  LoadOps`. Runs the decidable safety predicates over
                  the kernel-picked reservation; on success the
                  witness is fed to `LoadOps.runSafe`.

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
-- Builder: LoadPlan + bases + relocs → LoadOps tree.
-- ============================================================================

/-- Build the `LoadOps` tree from a `LoadPlan`, file handles, bases
    (from `Plan.assignBases`), the per-arch reloc formula, and the
    base-free `LoadRelocs`. Per segment: `setupSlots` + stores from
    `bakeSegmentRelocs`. -/
def build (lp : LoadPlan) (elfs : Array Elf)
    (h_elfs : elfs.size = lp.elfs.size)
    (handles : Array Runtime.FileHandle)
    (h_handles : handles.size = elfs.size)
    (bases : Array UInt64) (h_bases : bases.size = elfs.size)
    (formula : Formula) (relocPlan : LoadRelocs elfs.size) :
    Except String LoadOps := do
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
-- ============================================================================

/-- Gate the `LoadOps` tree through the decidable safety predicates
    (`MmapsDisjoint`, `MmapsContained`, `ZerosContained`,
    `StoresContained`, `MprotectsContained`) parameterized on the
    reservation `[rsvAddr, rsvAddr+rsvLen)`. Failure means a planner
    bug (the OS would otherwise raise SIGSEGV / mmap failure). -/
def safe (rsvAddr rsvLen : UInt64) (lo : LoadOps) :
    Except String { lo : LoadOps //
      MmapsDisjoint lo ∧
      MmapsContained rsvAddr rsvLen lo ∧
      ZerosContained rsvAddr rsvLen lo ∧
      StoresContained rsvAddr rsvLen lo ∧
      MprotectsContained rsvAddr rsvLen lo } :=
  if h : MmapsDisjoint lo ∧
         MmapsContained rsvAddr rsvLen lo ∧
         ZerosContained rsvAddr rsvLen lo ∧
         StoresContained rsvAddr rsvLen lo ∧
         MprotectsContained rsvAddr rsvLen lo then
    .ok ⟨lo, h⟩
  else
    .error "Materialize.safe: planned ops violate safety invariants \
      (loader bug — mmaps collide or extend outside the reservation)"

end LeanLoad.Materialize

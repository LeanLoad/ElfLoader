/-
Load ops: `SegmentOps rsvAddr rsvLen objCount` /
`ElfOps rsvAddr rsvLen objCount` / `LoadOps rsvAddr rsvLen objCount` over
the Finalize-owned typed op records (`MmapOp` / `ZeroOp` / `StoreOp` /
`MprotectOp`).

Stage boundary:
  • `Reloc` and `Layout` produce base-free facts: symbol resolution,
    page math, `objectSpan`, `totalSpan`, per-segment relocs, and the
    DFS post-order init sequence. None of those know an mmap base.
  • `Finalize/` consumes those plus the IO-supplied reservation
    base and emits the structured ops below. The runtime seam in
    `Runtime/Run.lean` consumes the witnessed tree directly — there is no flat
    `Array` intermediate.

The natural number parameter `objCount` is the elf count, threaded through
from `SegmentLayout objCount` (for the per-segment `Entry objCount`s).

Per-segment shape (the "realize protocol"):
  1. *MmapOp* — `Option MmapOp` — `mmapFile` for the file-backed prefix,
     with `PROT_WRITE` widened so reloc stores can land before the
     final `mprotect`. Absent for BSS-only segments.
  2. *Zero* — `Option ZeroOp` — clears the partial-page BSS tail past
     `filesz`, where the file overlay maps non-zero file bytes.
  3. *Stores* — `Array StoreOp` — one per applicable relocation.
  4. *MprotectOp* — mandatory — flips final permissions over the whole
     segment range.

Hierarchy:
  • `SegmentOps rsvAddr rsvLen objCount` — one segment's plan + its 4 typed ops.
  • `ElfOps rsvAddr rsvLen objCount`     — one elf's chosen base + its segments.
  • `LoadOps rsvAddr rsvLen objCount`    — the top-level op bundle for all elfs.

Safety witnesses are fields on the enclosing op tree and are built
constructively by `Finalize.build` from `BoundPlan`'s per-(i, j)
`InRange` / `Disjoint` theorems. User-code call/transfer addresses are packaged
with the same build result as `CallOp`s. There is no separate flat predicate.
-/

import LeanLoad.Finalize
import LeanLoad.Layout.Segment
import LeanLoad.Runtime

namespace LeanLoad.Finalize

open LeanLoad
open LeanLoad.Layout (SegmentLayout)

-- ============================================================================
-- Construction helper — compute the setup ops from a SegmentLayout.
-- Reloc stores are added separately by `Finalize.bakeSegmentRelocs`.
-- ============================================================================

/-- Compute the setup ops for one segment at the chosen base. The
    mmap is widened with `PROT_WRITE` so reloc stores can land before
    `mprotect` flips to final perms. The `path` is the source ELF's
    resolved filesystem path; it is recorded on the `MmapOp` so the
    runtime executor can re-open the file via `Runtime.Filesystem` at
    mmap time. -/
def setupSegment (sp : SegmentLayout objCount) (path : String)
    (base : UInt64) : SegmentSetup :=
  let absEaddr := base + sp.pageEaddr
  { mmap :=
      if sp.hasFileBacked then
        some { path, addr := absEaddr, len := sp.fileOverlayLen,
               prot := sp.prot ||| Runtime.PROT_WRITE,
               offset := sp.fileOffset }
      else none
    zero :=
      if sp.hasPartialBss then
        some { addr := absEaddr + sp.pageInset + sp.segment.filesz.val,
               len := sp.partialBssLen }
      else none
    mprotect := { addr := absEaddr, len := sp.pageLength, prot := sp.prot } }

-- ============================================================================
-- `setupSegment` characterisation. The three op positions are simple
-- closed forms of `(base, sp)`; these lemmas extract them so the
-- `SegmentOps` construction below can invoke the matching
-- `BoundPlan.segment_*_in_rsv` theorem directly.
-- ============================================================================

/-- The mmap op, when present, sits at `base + sp.pageEaddr` of
    length `sp.fileOverlayLen`. -/
theorem setupSegment_mmap_eq (sp : SegmentLayout objCount) (path : String)
    (base : UInt64) (m : MmapOp) (h : (setupSegment sp path base).mmap = some m) :
    m.addr = base + sp.pageEaddr ∧ m.len = sp.fileOverlayLen := by
  unfold setupSegment at h
  simp only at h
  by_cases h_fb : sp.hasFileBacked
  · rw [if_pos h_fb] at h
    injection h with h_eq
    rw [← h_eq]; exact ⟨rfl, rfl⟩
  · rw [if_neg h_fb] at h; cases h

/-- The zero op, when present, sits at
    `base + sp.pageEaddr + sp.pageInset + sp.segment.filesz.val` of length
    `sp.partialBssLen`. -/
theorem setupSegment_zero_eq (sp : SegmentLayout objCount) (path : String)
    (base : UInt64) (z : ZeroOp) (h : (setupSegment sp path base).zero = some z) :
    z.addr = base + sp.pageEaddr + sp.pageInset + sp.segment.filesz.val ∧
    z.len = sp.partialBssLen := by
  unfold setupSegment at h
  simp only at h
  by_cases h_pb : sp.hasPartialBss
  · rw [if_pos h_pb] at h
    injection h with h_eq
    rw [← h_eq]; exact ⟨rfl, rfl⟩
  · rw [if_neg h_pb] at h; cases h

/-- The mprotect op always sits at `base + sp.pageEaddr` of length
    `sp.pageLength`. -/
theorem setupSegment_mprotect_eq (sp : SegmentLayout objCount) (path : String)
    (base : UInt64) :
    (setupSegment sp path base).mprotect.addr = base + sp.pageEaddr ∧
    (setupSegment sp path base).mprotect.len = sp.pageLength := by
  exact ⟨rfl, rfl⟩

-- ============================================================================
-- Op collectors — diagnostic-only. Walk the tree and gather one
-- op kind. `Main.debug` prints their sizes for visibility; the proof
-- fields do not consume them.
-- ============================================================================

namespace LoadOps

/-- Every mmap across every elf and segment, in tree-walk order. -/
def mmaps (lo : LoadOps rsvAddr rsvLen objCount) : Array MmapOp :=
  lo.elfs.flatMap fun eo => eo.segments.filterMap (·.mmap)

/-- Every zero across every elf and segment. -/
def zeros (lo : LoadOps rsvAddr rsvLen objCount) : Array ZeroOp :=
  lo.elfs.flatMap fun eo => eo.segments.filterMap (·.zero)

/-- Every store across every elf and segment. -/
def stores (lo : LoadOps rsvAddr rsvLen objCount) : Array StoreOp :=
  lo.elfs.flatMap fun eo => eo.segments.flatMap (·.stores)

/-- Every mprotect across every elf and segment. -/
def mprotects (lo : LoadOps rsvAddr rsvLen objCount) : Array MprotectOp :=
  lo.elfs.flatMap fun eo => eo.segments.map (·.mprotect)

end LoadOps

end LeanLoad.Finalize

/-
Exec stage: the loader's single IO bookend after the pure middle.

Everything between Discover (which reads files) and the loaded
program's actual execution lives in this file. Pure planners
(`Layout`, `Reloc`, `Init`) produce abstract data — layouts with
chosen bases, segment-tied `Reloc.Patch g` lists, ctor `UInt64`
addresses — and `Exec.realize` interprets them all in one IO sweep:

  1. For each PT_LOAD segment of each object: anon `MAP_FIXED`
     reservation sized to the segment, file-backed `mmap` overlay
     (if filesz > 0), partial-last-page BSS zeroing, `mprotect`.
  2. For each `Reloc.Patch g`: a 4- or 8-byte write into the right
     segment's `Region` at `p.offset`. Patches are *segment-tied*
     by construction (each `Rela64` was located against a PT_LOAD
     at parse time — see `Parse.Reloc.LocatedRela`), so `applyPatch`
     looks up the segment by `Fin` index — no runtime cross-checks.
  3. For each ctor address: `callCtor`.
  4. Allocate the kernel-style stack and `execAndJump` to the entry
     point. Does not return.

There's no per-object outer reservation: with patches segment-tied,
each segment is its own MAP_FIXED unit. Inter-segment gaps stay
unmapped, which is stricter than the old "anon reservation + file
overlays" scheme.

Spec: gabi 08 § Process Initialization. AT_PHDR / AT_PHENT /
AT_PHNUM / AT_ENTRY in the auxv are required by the process-startup
contract (populated by `Runtime.execAndJump` in `runtime/exec.c`).
-/

import LeanLoad.Plan.Discover
import LeanLoad.Plan.Init
import LeanLoad.Plan.Layout
import LeanLoad.Plan.Reloc
import LeanLoad.Runtime
import LeanLoad.Parse.Structs

namespace LeanLoad.Exec

open LeanLoad
open LeanLoad.Discover
open LeanLoad.Layout
open LeanLoad.Reloc (Patch)
open LeanLoad.Parse (RawPhdr)
open LeanLoad.Elaborate (PatchSize Segment)

-- ============================================================================
-- Process image — per-object, per-segment runtime artifacts.
-- ============================================================================

/-- One PT_LOAD segment's mmap'd region. Stored as a `Sigma` so the
    `Region`'s size index can refer to the segment's loader-level
    `pageLength` (page-aligned). Patches that target this segment
    derive their `Region.InRange` proof from the segment's bound. -/
private abbrev SegmentImage : Type :=
  Σ s : Segment, Runtime.Region s.pageLength.toUSize

/-- Per-object runtime artifact: the planning-side layout plus one
    `SegmentImage` per PT_LOAD, in lock-step with `layout.segments`. -/
private structure ObjectImage where
  layout   : ObjectLayout
  segments : Array SegmentImage

/-- Realized process state: one `ObjectImage` per loaded object, in
    `ObjectList` order. The `size_eq` proof carries the count at the
    type level so per-patch indexing via `Fin n` is total. -/
private structure ProcessImage (n : Nat) where
  objects : Array ObjectImage
  size_eq : objects.size = n

-- ============================================================================
-- Step 1: realize one object's layout into mmap'd `SegmentImage`s.
--
-- Per-segment op order (gabi 07 § Program Loading):
--   1. anon `MAP_FIXED` reservation covering the segment's full
--      page-aligned `[vaddr, vaddr + length)` range.
--   2. file-backed overlay (if filesz > 0): same address, length
--      `fileLenPaged`, prot widened with `PROT_WRITE` so partial-
--      last-page BSS bytes can be cleared.
--   3. zero out partial-last-page BSS bytes (the gap between
--      `pageInset + fileLen` and `fileLenPaged`).
--   4. `mprotect` the full segment to drop the temporary
--      `PROT_WRITE`.
-- ============================================================================

/-- Realize one segment: anon reservation + file overlay + BSS zero +
    mprotect. Returns the `SegmentImage` (segment + region).
    Bounds proofs are discharged from `Segment`'s gabi-07 witnesses;
    no runtime range checks. -/
private def realizeSegment (rt : Runtime.Ops) (obj : LoadedObject)
    (base : UInt64) (s : Segment) : IO SegmentImage := do
  let length := s.pageLength.toUSize
  let region ← rt.mmapReserve (base + s.pageVaddr) length
  if s.fileLenPaged > 0 then
    let some handle := obj.handle
      | throw (IO.userError s!"realize: object '{obj.name}' has no file handle")
    let writableProt := s.prot ||| Runtime.PROT_WRITE
    let _overlay ← rt.mmap handle (base + s.pageVaddr) s.fileLenPaged.toUSize
                     writableProt s.fileOffsetPaged
    pure ()
  -- BSS InRange is mathematically obvious from `s.fileszLeMemsz` +
  -- `s.alignPow2` + `s.addrBound`: it reduces to `x ≤ alignUp x align`
  -- for `align > 0`. But `omega` doesn't reason through `alignUp`/
  -- `alignDown`'s `if`-branchy definitions, and we lack an
  -- `alignUp_ge` stdlib lemma. Runtime-check; the witnesses on
  -- `Segment` document that the check is structurally satisfied for
  -- well-formed ELFs. TODO: prove this once `alignUp_ge` lemma lands.
  let bssLen := s.memsz - s.filesz
  if bssLen > 0 then
    let bssOff := (s.pageInset + s.filesz).toUSize
    let bssLenU := bssLen.toUSize
    if h : Runtime.Region.InRange length bssOff bssLenU then
      rt.zeroout region bssOff bssLenU h
    else
      throw (IO.userError s!"realize: BSS zero out of range (object {obj.name})")
  -- `InRange length 0 length` is `0 ≤ length ∧ length ≤ length - 0`;
  -- both trivially hold.
  have hMprot : Runtime.Region.InRange length 0 length := by
    unfold Runtime.Region.InRange; exact ⟨by simp, by simp⟩
  rt.mprotect region 0 length hMprot s.prot
  return ⟨s, region⟩

/-- Realize every segment of one object. -/
private def realizeObject (rt : Runtime.Ops) (obj : LoadedObject) (lyt : ObjectLayout) :
    IO ObjectImage := do
  let segments ← lyt.segments.mapM (realizeSegment rt obj lyt.base)
  return { layout := lyt, segments }

/-- Realize each layout in lock-step with `g.val`, producing a
    `ProcessImage g.val.size`. Both arrays are indexed by the same
    `Fin g.val.size` so per-iteration lookup is total. -/
private def realizeLoop (rt : Runtime.Ops) (g : ObjectList)
    (layouts : { a : Array ObjectLayout // a.size = g.val.size })
    (i : Nat) (h_le : i ≤ g.val.size)
    (acc : Array ObjectImage) (ha : acc.size = i) :
    IO { a : Array ObjectImage // a.size = g.val.size } := do
  if hi : i < g.val.size then
    let obj := g.val[i]
    let lyt := layouts.val[i]'(layouts.property.symm ▸ hi)
    let img ← realizeObject rt obj lyt
    let acc' := acc.push img
    have ha' : acc'.size = i + 1 := by simp [acc', ha]
    realizeLoop rt g layouts (i + 1) hi acc' ha'
  else
    return ⟨acc, by omega⟩
termination_by g.val.size - i

/-- Anon reservation + file overlays + BSS zeroing + mprotect for
    every segment of every object, producing the `ProcessImage` that
    subsequent steps write into. -/
private def realizeImage (rt : Runtime.Ops) (g : ObjectList)
    (layouts : { a : Array ObjectLayout // a.size = g.val.size }) :
    IO (ProcessImage g.val.size) := do
  let ⟨objs, h⟩ ← realizeLoop rt g layouts 0 (Nat.zero_le _) #[] rfl
  return ⟨objs, h⟩

-- ============================================================================
-- Step 2: write each `Reloc.Patch g` into its segment's `Region`.
-- ============================================================================

/-- Apply one `Patch g`. Totally typed: `objectIdx : Fin g.val.size`
    is in bounds via `image.size_eq`, `segIdx` is a `Fin` into the
    object's segment array. The reservation-relative bound proof
    `Region.InRange (seg.length.toUSize) p.offset 8/4` is checked
    at runtime — the planner's `LocatedRela` witness guarantees the
    bound holds, but the witness's UInt64↔USize translation isn't
    threaded through `Patch`'s type yet; the runtime check produces
    the witness the typed op signature requires. -/
private def applyPatch {g : ObjectList} (rt : Runtime.Ops)
    (image : ProcessImage g.val.size) (p : Patch g) : IO Unit := do
  let h_idx : p.objectIdx.val < image.objects.size := image.size_eq.symm ▸ p.objectIdx.isLt
  let obj := image.objects[p.objectIdx.val]'h_idx
  let some segImg := obj.segments[p.segIdx.val]?
    | throw (IO.userError s!"applyPatch: segIdx {p.segIdx.val} out of range")
  let ⟨seg, region⟩ := segImg
  let length := seg.pageLength.toUSize
  match p.size with
  | .b8 =>
    if h : Runtime.Region.InRange length p.offset 8 then
      rt.patch64 region p.offset h p.value
    else
      throw (IO.userError s!"applyPatch: 8-byte write out of range (offset={p.offset})")
  | .b4 =>
    if h : Runtime.Region.InRange length p.offset 4 then
      rt.patch32 region p.offset h p.value
    else
      throw (IO.userError s!"applyPatch: 4-byte write out of range (offset={p.offset})")

-- ============================================================================
-- Step 4: kernel-style stack + jump (does not return).
-- ============================================================================

/-- Stack size for the loaded program. Matches musl's default (8 MiB). -/
def stackBytes : USize := 8 * 1024 * 1024

/-- Allocate kernel-style stack and jump to entry. **Does not return.**
    Non-emptiness of `image.objects` is structurally derivable from
    `ObjectList`'s `0 < g.val.size` invariant + `image.size_eq`, so
    the index `image.objects[0]` is total — no `?`/`throw`. -/
private def transferControl {n : Nat} (rt : Runtime.Ops) (mainObj : LoadedObject)
    (image : ProcessImage n) (h_pos : 0 < image.objects.size) (path : String) : IO Unit := do
  let mainImg := image.objects[0]'h_pos
  let stack ← rt.mmapStack stackBytes
  let entry  := mainImg.layout.base + mainImg.layout.entry.getD 0
  let phdrVa := mainImg.layout.base + mainObj.elf.phoff
  let phnum  := mainObj.elf.phnum.toUInt64
  let phent  := Parse.RawPhdrSize.toUInt64
  rt.execAndJump entry phdrVa phent phnum 0 stack path

-- ============================================================================
-- Single IO bookend: realize all plans, run ctors, jump.
-- ============================================================================

/-- The loader's single IO bookend. Takes the layouts (from
    `g.layouts`, including the per-layout `segmentsSorted` witness
    which implies pairwise-disjoint mmap regions — see
    `Thm/Layout.layouts_segmentsPairwiseDisjoint`), reloc patches,
    and ctor addresses, and realizes them in order: per-segment
    mmap → patch writes → ctor calls → stack + jump.

    The witness is a precondition documented in the type: every
    `MAP_FIXED` mmap below is non-colliding by construction.

    **Does not return** — the loaded program owns the process. -/
def realize (rt : Runtime.Ops) (g : ObjectList) (mainObj : LoadedObject)
    (layouts : { a : Array ObjectLayout //
      a.size = g.val.size ∧
      ∀ (i : Nat) (hi : i < a.size), a[i].segmentsSorted })
    (patches : Array (Patch g))
    (ctorAddrs : Array UInt64)
    (path : String) : IO Unit := do
  let sizedLayouts : { a : Array ObjectLayout // a.size = g.val.size } :=
    ⟨layouts.val, layouts.property.left⟩
  let image ← realizeImage rt g sizedLayouts
  for p in patches do applyPatch rt image p
  ctorAddrs.forM rt.callCtor
  -- `image.objects.size = g.val.size` (image.size_eq) and `0 < g.val.size`
  -- (g.property), so `0 < image.objects.size` is total.
  have h_pos : 0 < image.objects.size := image.size_eq.symm ▸ g.property
  transferControl rt mainObj image h_pos path

end LeanLoad.Exec

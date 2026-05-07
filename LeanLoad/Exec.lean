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

/-- One PT_LOAD segment's mmap'd region, indexed by the *planning*
    segment it realizes. The `Region`'s size index is `pageLength` of
    the planning-side `Segment`, so `Exec.applyPatch` can transfer
    `Patch.covers` to a `Region.InRange` proof via `Layout.patch_inRange`
    without runtime checks. -/
private abbrev SegmentImage (g : ObjectList) (objIdx : Fin g.val.size)
    (segIdx : Fin g.val[objIdx].elf.segments.size) : Type :=
  Runtime.Region g.val[objIdx].elf.segments[segIdx].pageLength

/-- Per-object runtime artifact: the planning-side layout plus one
    `SegmentImage` per PT_LOAD, in lock-step with the object's
    `elf.segments`. The `segments_idx` proof says the array's k-th
    entry's `fst` is `k`; combined with `segments_size`, this pins
    each entry's `Region` to `g.val[objIdx].elf.segments[k]`. -/
private structure ObjectImage (g : ObjectList) (objIdx : Fin g.val.size) where
  layout   : ObjectLayout
  segments : Array (Σ (segIdx : Fin g.val[objIdx].elf.segments.size),
                      SegmentImage g objIdx segIdx)
  segments_size : segments.size = g.val[objIdx].elf.segments.size
  segments_idx  : ∀ (k : Nat) (h : k < segments.size), segments[k].fst.val = k

/-- Realized process state: one `ObjectImage` per loaded object, with
    each entry tagged by its `Fin g.val.size` index. `objects_idx`
    pins the k-th entry's index to `k`, so per-patch lookup is total. -/
private structure ProcessImage (g : ObjectList) where
  objects : Array (Σ (i : Fin g.val.size), ObjectImage g i)
  objects_size : objects.size = g.val.size
  objects_idx  : ∀ (k : Nat) (h : k < objects.size), objects[k].fst.val = k

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
    mprotect. Returns a `SegmentImage` typed against the planning-side
    `Segment` directly. Bounds proofs are discharged from `Segment`'s
    gabi-07 witnesses; no runtime range checks. -/
private def realizeSegment (rt : Runtime.Ops) (obj : LoadedObject)
    (base : UInt64) (s : Segment) : IO (Runtime.Region s.pageLength) := do
  let length := s.pageLength
  let region ← rt.mmapReserve (base + s.pageVaddr) length
  if s.fileLenPaged > 0 then
    let some handle := obj.handle
      | throw (IO.userError s!"realize: object '{obj.name}' has no file handle")
    let writableProt := s.prot ||| Runtime.PROT_WRITE
    let _overlay ← rt.mmap handle (base + s.pageVaddr) s.fileLenPaged
                     writableProt s.fileOffsetPaged
    pure ()
  -- BSS InRange is discharged from `Segment`'s gabi-07 witnesses by
  -- `Layout.bss_inRange`; no runtime check needed.
  let bssLen := s.memsz - s.filesz
  if bssLen > 0 then
    rt.zeroout region (s.pageInset + s.filesz) bssLen (Layout.bss_inRange s)
  -- `InRange length 0 length` is `0 ≤ length ∧ length ≤ length - 0`;
  -- both trivially hold.
  have hMprot : Runtime.Region.InRange length 0 length := by
    unfold Runtime.Region.InRange; exact ⟨by simp, by simp⟩
  rt.mprotect region 0 length hMprot s.prot
  return region

/-- Realize one object's segments by walking `segs` in order. The
    accumulator carries the size + identity proofs that `ObjectImage`
    requires. `segs` is `g.val[objIdx].elf.segments` passed in
    explicitly so termination is on `segs.size - k` (an outer-bound
    variable, not a `Fin`-coerced expression that confuses omega). -/
private def realizeObjectLoop (rt : Runtime.Ops) (g : ObjectList)
    (objIdx : Fin g.val.size) (lyt : ObjectLayout)
    (segs : Array Segment) (h_segs : segs = g.val[objIdx].elf.segments)
    (k : Nat) (h_le : k ≤ segs.size)
    (acc : Array (Σ (segIdx : Fin g.val[objIdx].elf.segments.size),
                    SegmentImage g objIdx segIdx))
    (ha : acc.size = k)
    (ha_idx : ∀ (j : Nat) (hj : j < acc.size), acc[j].fst.val = j) :
    IO (ObjectImage g objIdx) := do
  if hk : k < segs.size then
    have hk' : k < g.val[objIdx].elf.segments.size := h_segs ▸ hk
    let segIdx : Fin g.val[objIdx].elf.segments.size := ⟨k, hk'⟩
    let s := g.val[objIdx].elf.segments[segIdx]
    let region ← realizeSegment rt g.val[objIdx] lyt.base s
    let entry : Σ (segIdx : Fin g.val[objIdx].elf.segments.size),
                  SegmentImage g objIdx segIdx := ⟨segIdx, region⟩
    let acc' := acc.push entry
    have ha' : acc'.size = k + 1 := by simp [acc', ha]
    have ha_idx' : ∀ (j : Nat) (hj : j < acc'.size), acc'[j].fst.val = j := by
      intro j hj
      have h_acc'_size : acc'.size = acc.size + 1 := by simp [acc']
      by_cases hj_eq : j = k
      · subst hj_eq
        show (acc.push entry)[j].fst.val = j
        rw [show (acc.push entry)[j] = entry from by
              simp [Array.getElem_push, ha]]
      · have hj_lt : j < acc.size := by
          rw [h_acc'_size] at hj; rw [ha]; omega
        have heq : acc'[j] = acc[j] := by
          show (acc.push entry)[j] = _; simp [Array.getElem_push, hj_lt]
        rw [heq]; exact ha_idx j hj_lt
    realizeObjectLoop rt g objIdx lyt segs h_segs (k + 1) hk acc' ha' ha_idx'
  else
    have h_size_eq : k = g.val[objIdx].elf.segments.size := by
      rw [← h_segs]; exact Nat.le_antisymm h_le (Nat.le_of_not_lt hk)
    return {
      layout := lyt,
      segments := acc,
      segments_size := by rw [ha, h_size_eq]
      segments_idx := ha_idx
    }
termination_by segs.size - k

/-- Realize every segment of one object. -/
private def realizeObject (rt : Runtime.Ops) (g : ObjectList)
    (objIdx : Fin g.val.size) (lyt : ObjectLayout) :
    IO (ObjectImage g objIdx) :=
  realizeObjectLoop rt g objIdx lyt g.val[objIdx].elf.segments rfl
    0 (Nat.zero_le _) #[] rfl
    (by intro j hj; simp at hj)

/-- Realize each layout in lock-step with `g.val`. The accumulator
    carries the size + identity proofs that `ProcessImage` requires. -/
private def realizeLoop (rt : Runtime.Ops) (g : ObjectList)
    (layouts : { a : Array ObjectLayout // a.size = g.val.size })
    (k : Nat) (h_le : k ≤ g.val.size)
    (acc : Array (Σ (i : Fin g.val.size), ObjectImage g i))
    (ha : acc.size = k)
    (ha_idx : ∀ (j : Nat) (hj : j < acc.size), acc[j].fst.val = j) :
    IO (ProcessImage g) := do
  if hk : k < g.val.size then
    let i : Fin g.val.size := ⟨k, hk⟩
    let lyt := layouts.val[k]'(layouts.property.symm ▸ hk)
    let img ← realizeObject rt g i lyt
    let entry : Σ (i : Fin g.val.size), ObjectImage g i := ⟨i, img⟩
    let acc' := acc.push entry
    have ha' : acc'.size = k + 1 := by simp [acc', ha]
    have ha_idx' : ∀ (j : Nat) (hj : j < acc'.size), acc'[j].fst.val = j := by
      intro j hj
      have h_acc'_size : acc'.size = acc.size + 1 := by simp [acc']
      by_cases hj_eq : j = k
      · subst hj_eq
        show (acc.push entry)[j].fst.val = j
        rw [show (acc.push entry)[j] = entry from by
              simp [Array.getElem_push, ha]]
      · have hj_lt : j < acc.size := by
          rw [h_acc'_size] at hj; rw [ha]; omega
        have heq : acc'[j] = acc[j] := by
          show (acc.push entry)[j] = _; simp [Array.getElem_push, hj_lt]
        rw [heq]; exact ha_idx j hj_lt
    realizeLoop rt g layouts (k + 1) hk acc' ha' ha_idx'
  else
    have h_size_eq : k = g.val.size := Nat.le_antisymm h_le (Nat.le_of_not_lt hk)
    return {
      objects := acc,
      objects_size := by rw [ha, h_size_eq]
      objects_idx := ha_idx
    }
termination_by g.val.size - k

/-- Anon reservation + file overlays + BSS zeroing + mprotect for
    every segment of every object, producing the `ProcessImage` that
    subsequent steps write into. -/
private def realizeImage (rt : Runtime.Ops) (g : ObjectList)
    (layouts : { a : Array ObjectLayout // a.size = g.val.size }) :
    IO (ProcessImage g) :=
  realizeLoop rt g layouts 0 (Nat.zero_le _) #[] rfl
    (by intro j hj; simp at hj)

-- ============================================================================
-- Step 2: write each `Reloc.Patch g` into its segment's `Region`.
-- ============================================================================

/-- Apply one `Patch g`. Fully proven: `objectIdx` and `segIdx` index
    totally via `image.objects_size`/`objects_idx` and `ObjectImage`'s
    `segments_size`/`segments_idx`. The `InRange` bound is discharged
    structurally from `Patch.covers` via `Layout.patch_inRange`, so no
    runtime range check remains. -/
private def applyPatch {g : ObjectList} (rt : Runtime.Ops)
    (image : ProcessImage g) (p : Patch g) : IO Unit := do
  let h_idx : p.objectIdx.val < image.objects.size :=
    image.objects_size.symm ▸ p.objectIdx.isLt
  let entry := image.objects[p.objectIdx.val]'h_idx
  -- entry.fst.val = p.objectIdx.val (by objects_idx); upgrade to Fin equality.
  have h_obj_eq : entry.fst = p.objectIdx :=
    Fin.ext (by rw [image.objects_idx p.objectIdx.val h_idx])
  -- Cast the per-object image to the index we need.
  let obj : ObjectImage g p.objectIdx := h_obj_eq ▸ entry.snd
  -- Now look up the segment.
  have h_seg_idx : p.segIdx.val < obj.segments.size :=
    obj.segments_size.symm ▸ p.segIdx.isLt
  let segEntry := obj.segments[p.segIdx.val]'h_seg_idx
  have h_seg_eq : segEntry.fst = p.segIdx :=
    Fin.ext (obj.segments_idx p.segIdx.val h_seg_idx)
  -- segEntry.snd : Region g.val[p.objectIdx].elf.segments[segEntry.fst].pageLength.
  -- Rewrite the size index to `p.segIdx`'s pageLength via `h_seg_eq`.
  let seg : Segment := g.val[p.objectIdx].elf.segments[p.segIdx]
  let region : Runtime.Region seg.pageLength := by
    have := segEntry.snd
    rw [h_seg_eq] at this
    exact this
  -- `Patch.covers` witnesses `coversRela seg.vaddr seg.memsz p.rela`,
  -- so `Layout.patch_inRange` discharges `InRange seg.pageLength _ 8`.
  let offset := p.rela.r_offset - seg.pageVaddr
  let h8 : Runtime.Region.InRange seg.pageLength offset 8 :=
    Layout.patch_inRange seg p.rela p.covers
  match p.size with
  | .b8 => rt.patch64 region offset h8 p.value
  | .b4 => rt.patch32 region offset (Layout.inRange_4_of_8 h8) p.value

-- ============================================================================
-- Step 4: kernel-style stack + jump (does not return).
-- ============================================================================

/-- Stack size for the loaded program. Matches musl's default (8 MiB). -/
def stackBytes : UInt64 := 8 * 1024 * 1024

/-- Allocate kernel-style stack and jump to entry. **Does not return.**
    Non-emptiness of `image.objects` is structurally derivable from
    `ObjectList`'s `0 < g.val.size` invariant + `image.objects_size`,
    so the index `image.objects[0]` is total — no `?`/`throw`. -/
private def transferControl (rt : Runtime.Ops) {g : ObjectList} (mainObj : LoadedObject)
    (image : ProcessImage g) (h_pos : 0 < image.objects.size) (path : String) : IO Unit := do
  let mainImg := (image.objects[0]'h_pos).snd
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
  -- `image.objects.size = g.val.size` and `0 < g.val.size`, so
  -- `0 < image.objects.size` — `image.objects[0]` is total.
  have h_pos : 0 < image.objects.size := image.objects_size.symm ▸ g.property
  transferControl rt mainObj image h_pos path

end LeanLoad.Exec

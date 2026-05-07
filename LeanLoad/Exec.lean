/-
Exec stage: the loader's single IO bookend after the pure middle.

Everything between Discover (which reads files) and the loaded
program's actual execution lives in this file. Pure planners
(`Layout`, `Reloc`, `Init`) produce abstract data — layouts with
chosen bases, `Reloc.Patch n` lists, ctor `UInt64` addresses — and
`Exec.realize` interprets them all in one IO sweep:

  1. For each `ObjectLayout`: anonymous reservation, file-backed
     `mmap` overlays per segment (kernel does the file→memory
     mapping; no userspace memcpy), BSS zeroing for partial-last-page
     bytes, `mprotect` per segment.
  2. For each `Reloc.Patch n`: a 4- or 8-byte write into the right
     reservation at `targetVa - layout.base`.
  3. For each ctor address: `callCtor`.
  4. Allocate the kernel-style stack and `execAndJump` to the entry
     point. Does not return.

No byte mutation happens before this point — the middle is pure
data, and `realize` is the trust seam. The per-segment op sequence
(overlay/bssZero/mprotect) is derived inline from `lyt.segments` —
there's no separate `MapPlan` stage because that planning was
trivial (a function of segment shape) and only `realize` consumed it.

The `ObjectImage` / `ProcessImage` data types used internally to
thread mapped regions across the realize stages are inlined here —
they have no other consumers since the middle is plan-only.

Spec: gabi 08 § Process Initialization. AT_PHDR / AT_PHENT /
AT_PHNUM / AT_ENTRY in the auxv are required by the process-startup
contract (populated by `Runtime.execAndJump` in `runtime/exec.c`).
-/

import LeanLoad.Plan.Discover
import LeanLoad.Plan.Init
import LeanLoad.Plan.Layout
import LeanLoad.Plan.Reloc
import LeanLoad.Runtime
import LeanLoad.Spec.Program

namespace LeanLoad.Exec

open LeanLoad
open LeanLoad.Discover
open LeanLoad.Layout
open LeanLoad.Reloc (Patch)
open LeanLoad.Spec.Reloc (PatchSize)

-- ============================================================================
-- Process image — internal data structure threaded through the realize
-- stages. Pairs a per-object layout with its mmap'd `Region`s so
-- patch-writes and exec-stack-build can index by `Fin n` without a
-- separate cross-array invariant.
-- ============================================================================

/-- Per-object runtime artifact: planning-side `ObjectLayout` plus
    the mmap'd `Region`s. -/
private structure ObjectImage where
  /-- Layout (where the object lives in VA space). -/
  layout : ObjectLayout
  /-- Anon `MAP_FIXED` reservation covering `[layout.base,
      layout.base + objectSpan layout.segments)`. -/
  reservation : Runtime.Region
  /-- One file-backed `Region` per segment with `fileLenPaged > 0`
      (aligned with `layout.segments`; `none` for BSS-only segments
      that have no file overlay). -/
  segments    : Array (Option Runtime.Region)

/-- Realized process state: one `ObjectImage` per loaded object, in
    `ObjectList` order. The `size_eq` proof carries the count at the
    type level so per-patch indexing via `Fin n` is total. -/
private structure ProcessImage (n : Nat) where
  objects : Array ObjectImage
  size_eq : objects.size = n

-- ============================================================================
-- Step 1: realize one object's layout into mmap'd `Region`s.
--
-- Per-object op order (gabi 07 § Program Loading):
--   1. anon `MAP_FIXED` reservation covering the full object span.
--   2. for each segment: file-backed overlay (if filesz > 0) +
--      BSS zeroing (if memsz > filesz).
--   3. for each segment: `mprotect` to drop the temporary
--      `PROT_WRITE` we widened the overlay with.
-- ============================================================================

/-- Realize one object's layout: build the reservation, copy in file
    bytes, zero BSS, drop write permission. The threaded
    `segs.size = lyt.segments.size` invariant makes `Array.set`
    total — no `set!`/panic seam. -/
private def realizeObject (rt : Runtime.Ops) (obj : LoadedObject) (lyt : ObjectLayout) :
    IO ObjectImage := do
  let reservation ← rt.mmapReserve lyt.base lyt.span.toUSize
  -- `segs` carries `size = lyt.segments.size` as a subtype so `set`
  -- (not `set!`) discharges the bounds check at each overlay.
  let mut segs : { a : Array (Option Runtime.Region) //
                   a.size = lyt.segments.size } :=
    ⟨Array.replicate lyt.segments.size none, by simp⟩
  -- Pass 1: per-segment overlay + BSS zeroing.
  for h : i in [:lyt.segments.size] do
    let s := lyt.segments[i]
    if s.fileLenPaged > 0 then
      let some handle := obj.handle
        | throw (IO.userError s!"realize: object '{obj.name}' has no file handle")
      let writableProt := s.prot ||| Runtime.PROT_WRITE
      let r ← rt.mmapAt handle (lyt.base + s.vaddr) s.fileLenPaged.toUSize
                writableProt s.fileOffsetPaged
      have h_idx : i < segs.val.size := segs.property.symm ▸ h.upper
      segs := ⟨segs.val.set i (some r) h_idx,
               by simp [Array.size_set, segs.property]⟩
    let bssLen := s.phdr.p_memsz - s.fileLen
    if bssLen > 0 then
      let bssOff := (s.vaddr + s.pageInset + s.fileLen).toUSize
      rt.zeroout reservation bssOff bssLen.toNat.toUSize
  -- Pass 2: per-segment mprotect (drops the temporary PROT_WRITE).
  for s in lyt.segments do
    rt.mprotect reservation s.vaddr.toUSize s.length.toUSize s.prot
  return { layout := lyt, reservation, segments := segs.val }

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

/-- Anonymous reservation + file-backed mmap overlays + BSS zeroing
    + mprotect for every object, producing the `ProcessImage` that
    subsequent steps write into. -/
private def realizeImage (rt : Runtime.Ops) (g : ObjectList)
    (layouts : { a : Array ObjectLayout // a.size = g.val.size }) :
    IO (ProcessImage g.val.size) := do
  let ⟨objs, h⟩ ← realizeLoop rt g layouts 0 (Nat.zero_le _) #[] rfl
  return ⟨objs, h⟩

-- ============================================================================
-- Step 2: write each `Reloc.Patch` into its object's reservation.
-- ============================================================================

/-- Apply one `Patch n`. Totally typed: `objectIdx : Fin n` is in
    bounds via `image.size_eq`; bounds inside the region are
    enforced by `Reloc.Patch.inRange` at planning time; width is
    `PatchSize` (4 or 8 only). -/
private def applyPatch {n : Nat} (rt : Runtime.Ops) (image : ProcessImage n)
    (p : Patch n) : IO Unit :=
  let h : p.objectIdx.val < image.objects.size := image.size_eq.symm ▸ p.objectIdx.isLt
  let obj := image.objects[p.objectIdx.val]'h
  let offset := (p.targetVa - obj.layout.base).toUSize
  match p.size with
  | .b8 => rt.patch64 obj.reservation offset p.value
  | .b4 => rt.patch32 obj.reservation offset p.value

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
  let phdrVa := mainImg.layout.base + mainObj.elf.header.e_phoff
  let phnum  := mainObj.elf.header.e_phnum.toUInt64
  let phent  := Spec.Program.entrySize.toUInt64
  rt.execAndJump entry phdrVa phent phnum 0 stack path

-- ============================================================================
-- Single IO bookend: realize all plans, run ctors, jump.
-- ============================================================================

/-- The loader's single IO bookend. Takes the layouts (from
    `g.layouts`), reloc patches, and ctor addresses, and realizes
    them in order: mmap + zeroout + mprotect → patch writes →
    ctor calls → stack + jump.

    **Does not return** — the loaded program owns the process. -/
def realize (rt : Runtime.Ops) (g : ObjectList) (mainObj : LoadedObject)
    (layouts : { a : Array ObjectLayout // a.size = g.val.size })
    (patches : Array (Patch g.val.size))
    (ctorAddrs : Array UInt64)
    (path : String) : IO Unit := do
  let image ← realizeImage rt g layouts
  for p in patches do applyPatch rt image p
  ctorAddrs.forM rt.callCtor
  -- `image.objects.size = g.val.size` (image.size_eq) and `0 < g.val.size`
  -- (g.property), so `0 < image.objects.size` is total.
  have h_pos : 0 < image.objects.size := image.size_eq.symm ▸ g.property
  transferControl rt mainObj image h_pos path

end LeanLoad.Exec

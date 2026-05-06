/-
Map: place each object's `PT_LOAD` segments at the address Layout
chose. `MAP_FIXED` everywhere — no kernel-chosen bases.

Per-object flow:

  1. Anon `MAP_FIXED` reservation at `lyt.base` for `objectSpan` —
     RW; zero-fills BSS-only pages + inter-segment gaps "for free"
     (kernel-zeroed anonymous pages).
  2. For each segment with `fileLenPaged > 0`:
     - File-backed `MAP_PRIVATE | MAP_FIXED` overlay at
       `lyt.base + s.vaddr` for `fileLenPaged` bytes from
       `fileOffsetPaged`, with `s.prot ||| PROT_WRITE` (writable so
       step 3 can zero partial-last-page BSS).
     - Memset zero the partial-last-page BSS: bytes from
       `pageInset + fileLen` to `pageInset + memsz`. Skipped if
       `memsz = fileLen`.
  3. `mprotectRange` each segment's full range to `s.prot` (drops
     the temporary `PROT_WRITE` if `s.prot` doesn't include it).

For `ET_EXEC`, `lyt.base` covers the absolute span; `s.vaddr` is
within that range. For `ET_DYN`, `lyt.base` comes from
`Layout.assignBases` (anchor + cumulative). All addresses are
absolute by Map's IO time.

The IO writes that follow (relocation patches) live in `Apply.lean`.
-/

import LeanLoad.Discover
import LeanLoad.Layout
import LeanLoad.Reloc
import LeanLoad.Runtime

namespace LeanLoad.Map

open LeanLoad
open LeanLoad.Discover
open LeanLoad.Layout

/-- A `ByteArray` of `n` zero bytes. Used by Map for partial-last-page
    BSS clears; small (typically ≤ one page). -/
private def zeroBytes (n : Nat) : ByteArray :=
  ⟨Array.replicate n 0⟩

/-- Runtime artifact for one mapped object: the anon `reservation`
    (covers the whole `[base, base + objectSpan)`) plus one
    file-backed `Region` per segment with `fileLenPaged > 0` (aligned
    with `Layout.ObjectLayout.segments`, with `none` for BSS-only
    segments that have no file overlay). -/
structure ObjectImage where
  reservation : Runtime.Region
  segments    : Array (Option Runtime.Region)

/-- Output of the Map stage. Pairs each `Layout.ObjectLayout` with
    the `Region`s Map produced; downstream Apply / Exec read both the
    layout-side data (bases, segments) and the runtime artifacts. -/
structure ProcessImage where
  layouts : Array ObjectLayout
  objects : Array ObjectImage

/-- Map every segment of one object at its Layout-assigned `base`,
    returning the produced `ObjectImage`. -/
def mapObject (g : DepGraph) (lyt : ObjectLayout) : IO ObjectImage := do
  let some obj := g.objects[lyt.objectIdx]?
    | throw (IO.userError s!"mapObject: missing {lyt.objectIdx}")
  let some h := obj.handle
    | throw (IO.userError s!"mapObject: object {lyt.objectIdx} has no file handle")
  -- Step 1: anon reservation (zero pages for BSS-only + inter-segment gaps).
  let reservation ← Runtime.mmapAnonFixed lyt.base lyt.span.toUSize
  -- Step 2: file-backed overlay + partial-page BSS zero per segment.
  let mut segs : Array (Option Runtime.Region) := Array.mkEmpty lyt.segments.size
  for s in lyt.segments do
    let segRegion : Option Runtime.Region ←
      if s.fileLenPaged > 0 then
        let writableProt := s.prot ||| Runtime.PROT_WRITE
        let r ← Runtime.mmapAt h (lyt.base + s.vaddr) s.fileLenPaged.toUSize
                  writableProt s.fileOffsetPaged
        pure (some r)
      else pure none
    segs := segs.push segRegion
    let bssLen := s.phdr.p_memsz - s.fileLen
    if bssLen > 0 then
      let bssOff := (s.vaddr + s.pageInset + s.fileLen).toUSize
      Runtime.write reservation bssOff (zeroBytes bssLen.toNat)
  -- Step 3: drop PROT_WRITE for read-only / read-execute segments.
  for s in lyt.segments do
    Runtime.mprotectRange reservation s.vaddr.toUSize s.length.toUSize s.prot
  return { reservation, segments := segs }

/-- Map every object in a link map; return the full `ProcessImage`. -/
def mapAll (g : DepGraph) (layouts : Array ObjectLayout) : IO ProcessImage := do
  let mut objects : Array ObjectImage := Array.mkEmpty layouts.size
  for lyt in layouts do
    objects := objects.push (← mapObject g lyt)
  return { layouts, objects }

-- ============================================================================
-- Integration test runner. Sanity-checks that one ObjectImage comes
-- back per object.
-- ============================================================================

def test (g : DepGraph) (layouts : Array ObjectLayout) : IO Nat := do
  let image ← mapAll g layouts
  let mut failures := 0
  if image.objects.size != g.objects.size then
    IO.eprintln s!"image.objects.size {image.objects.size} ≠ object count {g.objects.size}"
    failures := failures + 1
  return failures

end LeanLoad.Map

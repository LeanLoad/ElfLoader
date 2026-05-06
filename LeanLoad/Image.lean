/-
Process image: runtime artifacts produced by `MapApply` and consumed
by `RelocApply` / `Exec`.

`ObjectImage` carries both the per-object *layout* (where it lives
in VA space) *and* the runtime mapped `Region`s. Pairing them
removes the redundant `[i]?` lookups in `RelocApply` / `Exec` —
"object N has both a layout and an image" is now a single
structural fact rather than a cross-array invariant.

`MapApply` constructs `ProcessImage`; `RelocApply` / `Exec` read
fields. Putting these types here (rather than in `MapApply`) makes
the consumers *peers* of MapApply, not downstream importers.
-/

import LeanLoad.Layout
import LeanLoad.Runtime

namespace LeanLoad.Map

open LeanLoad
open LeanLoad.Layout

/-- Per-object runtime artifact: the planning-side `ObjectLayout`
    plus the mmap'd `Region`s. Single source of truth — every loaded
    object has exactly one of these, and consumers don't have to
    keep two parallel arrays in sync. -/
structure ObjectImage where
  /-- Layout (where the object lives in VA space). -/
  layout : ObjectLayout
  /-- Anon `MAP_FIXED` reservation covering `[layout.base,
      layout.base + objectSpan layout.segments)`. -/
  reservation : Runtime.Region
  /-- One file-backed `Region` per segment with `fileLenPaged > 0`
      (aligned with `layout.segments`, with `none` for BSS-only
      segments that have no file overlay). -/
  segments    : Array (Option Runtime.Region)

/-- Output of the Map stage: one `ObjectImage` per loaded object,
    in `ObjectList.objects` order. Parameterised by the dep graph's
    object count `n`; the `size_eq` proof carries the size at the
    type level so consumers (`RelocApply`, `Exec`) can index into
    `objects` totally with `Fin n` — no `?`/`throw`. -/
structure ProcessImage (n : Nat) where
  objects : Array ObjectImage
  size_eq : objects.size = n

/-- Bases array (per-object). Used for diagnostics and Exec's main
    entry-point computation. -/
def ProcessImage.bases (image : ProcessImage n) : Array UInt64 :=
  image.objects.map (·.layout.base)

end LeanLoad.Map

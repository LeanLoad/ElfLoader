/-
Apply: walk the planned `Patch`es and poke bytes into mmap'd
memory. Trusted IO; the *what* is decided by `LeanLoad.Reloc`'s pure
planner. The runtime exposes only typed primitives — `Runtime.patch64`
and `Runtime.patch32` — so the "unsupported width" branch that used
to live here can't even be expressed.
-/

import LeanLoad.DiscoverPlan
import LeanLoad.Image
import LeanLoad.Layout
import LeanLoad.RelocPlan
import LeanLoad.Resolve
import LeanLoad.Runtime

namespace LeanLoad.Apply

open LeanLoad
open LeanLoad.Discover
open LeanLoad.Layout

/-- Apply one `Patch n` by writing into its object's reservation
    `Region` at `offset = p.targetVa - obj.layout.base`. Total
    indexing — `Patch n`'s `objectIdx : Fin n` and
    `ProcessImage n`'s `size_eq : objects.size = n` together let us
    use `image.objects[p.objectIdx]` without `?` or `throw`.

    **Trust seam.** Bounds are proven structurally:
    - `p.objectIdx.val < image.objects.size`: from `p.objectIdx : Fin n`
      and `image.size_eq : image.objects.size = n`.
    - `p.targetVa ∈ [obj.layout.base, obj.layout.base + lyt.span)`:
      enforced by `Patch.inRange` in `Reloc.planRela`.
    - `p.size ∈ {4, 8}`: proven by `Thm.formula_size_valid` for any
      verified per-arch formula. (Width branch defaults non-`8` to
      `4` — the only other valid width.) -/
def applyPatch {n : Nat} (image : Map.ProcessImage n) (p : Reloc.Patch n) : IO Unit :=
  let h : p.objectIdx.val < image.objects.size := image.size_eq.symm ▸ p.objectIdx.isLt
  let obj := image.objects[p.objectIdx.val]'h
  let offset := (p.targetVa - obj.layout.base).toUSize
  if p.size = 8 then
    Runtime.patch64 obj.reservation offset p.value
  else
    Runtime.patch32 obj.reservation offset p.value

/-- Apply every planned patch. With `n` matched between image and
    patches at the type level, no per-patch bounds checks needed. -/
def applyPatches {n : Nat} (image : Map.ProcessImage n) (patches : Array (Reloc.Patch n)) :
    IO Unit := do
  for p in patches do applyPatch image p

end LeanLoad.Apply

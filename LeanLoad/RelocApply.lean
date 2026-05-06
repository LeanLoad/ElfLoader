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
    `Region` at `offset = p.targetVa - obj.layout.base`. Totally
    typed — every precondition is in the type, no `?`/`throw`/branch
    on a runtime tag.

    **Trust seam.** All preconditions are structural:
    - `p.objectIdx.val < image.objects.size`: from `p.objectIdx : Fin n`
      and `image.size_eq : image.objects.size = n`.
    - `p.targetVa ∈ [obj.layout.base, obj.layout.base + lyt.span)`:
      enforced by `Patch.inRange` in `Reloc.planRela` (re-checked
      here would only repeat the planner's invariant).
    - Width is 4 or 8: `p.size : PatchSize` only has those two
      constructors, so the dispatch below is exhaustive — no
      "unsupported width" branch can exist. -/
def applyPatch {n : Nat} (rt : Runtime.Ops) (image : Map.ProcessImage n)
    (p : Reloc.Patch n) : IO Unit :=
  let h : p.objectIdx.val < image.objects.size := image.size_eq.symm ▸ p.objectIdx.isLt
  let obj := image.objects[p.objectIdx.val]'h
  let offset := (p.targetVa - obj.layout.base).toUSize
  match p.size with
  | .b8 => rt.patch64 obj.reservation offset p.value
  | .b4 => rt.patch32 obj.reservation offset p.value

/-- Apply every planned patch. With `n` matched between image and
    patches at the type level, no per-patch bounds checks needed. -/
def applyPatches {n : Nat} (rt : Runtime.Ops) (image : Map.ProcessImage n)
    (patches : Array (Reloc.Patch n)) : IO Unit := do
  for p in patches do applyPatch rt image p

end LeanLoad.Apply

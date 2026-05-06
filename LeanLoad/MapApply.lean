/-
Map executor — trusted IO.

Walks the `Map.ObjectPlan` sequence produced by `Map.plan` (in
`MapPlan`) and performs the actual `mmap` / `mprotect` / write
syscalls, producing a `ProcessImage` with the per-object `Region`
artifacts. Plan / apply split mirrors `Reloc.plan` / `Apply`.

Per-object iteration: `apply` processes one object at a time,
producing one `ObjectImage` per `ObjectPlan`. The reservation is
made first and held in scope while the object's ops execute, so the
awkward "did we set the reservation yet?" check is gone — there's
no `Option`-of-`Region` accumulator.

For `ET_EXEC`, `lyt.base` covers the absolute span; `s.vaddr` is
within that range. For `ET_DYN`, `lyt.base` comes from
`Layout.assignBases` (anchor + cumulative). All addresses are
absolute by Map's IO time.
-/

import LeanLoad.DiscoverPlan
import LeanLoad.Image
import LeanLoad.Layout
import LeanLoad.MapPlan
import LeanLoad.Runtime

namespace LeanLoad.Map

open LeanLoad
open LeanLoad.Discover
open LeanLoad.Layout
open LeanLoad.Parse.Segment

/-- Apply one object's planned ops, producing its `ObjectImage`.
    Takes the `LoadedObject` directly (caller looked it up) — no
    `g[i]?` throw inside.

    The `overlay`'s `segIdx : Fin plan.layout.segments.size` plus
    `segs := Array.replicate plan.layout.segments.size none` makes
    `set!` structurally unreachable as a panic — the type system
    knows `segIdx.val < plan.layout.segments.size`, and the size
    matches at construction. (We use `set!` rather than `set` because
    Lean's mutable-`for` doesn't propagate the size invariant through
    the loop accumulator; the Fin still documents the intent.) -/
private def applyObject (rt : Runtime.Ops) (obj : LoadedObject) (plan : ObjectPlan) :
    IO ObjectImage := do
  let reservation ← rt.mmapAnonFixed plan.layout.base plan.layout.span.toUSize
  let mut segs : Array (Option Runtime.Region) :=
    Array.replicate plan.layout.segments.size none
  for op in plan.ops do
    match op with
    | .overlay segIdx addr len fileOff prot =>
      let some h := obj.handle
        | throw (IO.userError s!"apply: object '{obj.name}' has no file handle")
      let r ← rt.mmapAt h addr len prot fileOff
      segs := segs.set! segIdx.val (some r)
    | .bssZero offset len =>
      rt.zeroout reservation offset len
    | .mprotect offset len prot =>
      rt.mprotectRange reservation offset len prot
  return { layout := plan.layout, reservation, segments := segs }

/-- Helper: push images into an accumulator from index `i` onward,
    threading the invariants `i ≤ g.val.size` and `acc.size = i`.
    Indexes both `g` and `plans` by the same `Fin` — total
    lookup, no `?`, no throws. The result has size `g.val.size`
    *by construction*. -/
private def applyLoop (rt : Runtime.Ops) (g : ObjectList)
    (plans : { a : Array ObjectPlan // a.size = g.val.size })
    (i : Nat) (h_le : i ≤ g.val.size)
    (acc : Array ObjectImage) (ha : acc.size = i) :
    IO { a : Array ObjectImage // a.size = g.val.size } := do
  if hi : i < g.val.size then
    let obj := g.val[i]
    let plan := plans.val[i]'(plans.property.symm ▸ hi)
    let img ← applyObject rt obj plan
    let acc' := acc.push img
    have ha' : acc'.size = i + 1 := by simp [acc', ha]
    applyLoop rt g plans (i + 1) hi acc' ha'
  else
    return ⟨acc, by omega⟩
termination_by g.val.size - i

/-- Execute a planned op sequence against the process address space.
    The only function in the Map stage that calls `Runtime.mmap*` —
    `plan` produced the description, `apply` performs the syscalls.

    Takes sized plans (matching `g.val.size`) so per-iteration
    indexing into both `g` and `plans` is total. Returns
    `ProcessImage g.val.size` by construction. -/
def apply (rt : Runtime.Ops) (g : ObjectList)
    (plans : { a : Array ObjectPlan // a.size = g.val.size }) :
    IO (ProcessImage g.val.size) := do
  let ⟨objs, h⟩ ← applyLoop rt g plans 0 (Nat.zero_le _) #[] rfl
  return ⟨objs, h⟩

/-- Plan + apply in one go. Convenience wrapper for the loader pipeline.

    Takes the enriched `layouts` returned by `g.layouts` — its property
    bundles `layouts.val.size = g.val.size` (used here) with the per-layout
    `segmentsSorted` witness (used downstream by Thm). Returns
    `ProcessImage g.val.size` *by construction* — no runtime size check,
    the type system enforces it. -/
def mapAll (rt : Runtime.Ops) (g : ObjectList)
    (layouts : { a : Array ObjectLayout //
      a.size = g.val.size ∧ ∀ (i : Nat) (h : i < a.size), a[i].segmentsSorted }) :
    IO (ProcessImage g.val.size) := do
  -- `plan` is `Array.map`, so `(plan layouts.val).size = layouts.val.size = g.val.size`.
  let plans : { a : Array ObjectPlan // a.size = g.val.size } :=
    ⟨plan layouts.val, by simp [plan, layouts.property.left]⟩
  apply rt g plans

end LeanLoad.Map

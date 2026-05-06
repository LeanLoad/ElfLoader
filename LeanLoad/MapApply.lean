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
    `g.objects[i]?` throw inside. -/
private def applyObject (obj : LoadedObject) (plan : ObjectPlan) : IO ObjectImage := do
  let reservation ← Runtime.mmapAnonFixed plan.layout.base plan.layout.span.toUSize
  let mut segs : Array (Option Runtime.Region) :=
    Array.replicate plan.layout.segments.size none
  for op in plan.ops do
    match op with
    | .overlay segIdx addr len fileOff prot =>
      let some h := obj.handle
        | throw (IO.userError s!"apply: object '{obj.name}' has no file handle")
      let r ← Runtime.mmapAt h addr len prot fileOff
      segs := segs.set! segIdx (some r)
    | .bssZero offset len =>
      Runtime.zeroout reservation offset len
    | .mprotect offset len prot =>
      Runtime.mprotectRange reservation offset len prot
  return { layout := plan.layout, reservation, segments := segs }

/-- Helper: push images into an accumulator from index `i` onward,
    threading the invariants `i ≤ g.objects.size` and `acc.size = i`.
    Indexes both `g.objects` and `plans` by the same `Fin` — total
    lookup, no `?`, no throws. The result has size `g.objects.size`
    *by construction*. -/
private def applyLoop (g : DepGraph)
    (plans : { a : Array ObjectPlan // a.size = g.objects.size })
    (i : Nat) (h_le : i ≤ g.objects.size)
    (acc : Array ObjectImage) (ha : acc.size = i) :
    IO { a : Array ObjectImage // a.size = g.objects.size } := do
  if hi : i < g.objects.size then
    let obj := g.objects[i]
    let plan := plans.val[i]'(plans.property.symm ▸ hi)
    let img ← applyObject obj plan
    let acc' := acc.push img
    have ha' : acc'.size = i + 1 := by simp [acc', ha]
    applyLoop g plans (i + 1) hi acc' ha'
  else
    return ⟨acc, by omega⟩
termination_by g.objects.size - i

/-- Execute a planned op sequence against the process address space.
    The only function in the Map stage that calls `Runtime.mmap*` —
    `plan` produced the description, `apply` performs the syscalls.

    Takes sized plans (matching `g.objects.size`) so per-iteration
    indexing into both `g.objects` and `plans` is total. Returns
    `ProcessImage g.objects.size` by construction. -/
def apply (g : DepGraph)
    (plans : { a : Array ObjectPlan // a.size = g.objects.size }) :
    IO (ProcessImage g.objects.size) := do
  let ⟨objs, h⟩ ← applyLoop g plans 0 (Nat.zero_le _) #[] rfl
  return ⟨objs, h⟩

/-- Plan + apply in one go. Convenience wrapper for the loader pipeline.

    Takes a *sized* `layouts` (the return type of `g.layouts`); the
    `layouts.property` proof carries `layouts.val.size = g.objects.size`.
    Returns `ProcessImage g.objects.size` *by construction* — no
    runtime size check, the type system enforces it. -/
def mapAll (g : DepGraph)
    (layouts : { a : Array ObjectLayout // a.size = g.objects.size }) :
    IO (ProcessImage g.objects.size) := do
  -- `plan` is `Array.map`, so `(plan layouts.val).size = layouts.val.size = g.objects.size`.
  let plans : { a : Array ObjectPlan // a.size = g.objects.size } :=
    ⟨plan layouts.val, by simp [plan, layouts.property]⟩
  apply g plans

end LeanLoad.Map

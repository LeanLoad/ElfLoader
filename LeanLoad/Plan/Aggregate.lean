/-
Top-level pure-pipeline aggregate.

A `Plan` bundles the four base-free planner outputs under one
structure parameterised by the object count `objects.val.size`:

  · `objects   : ObjectList` — main + transitive deps in BFS order.
                 Carries non-emptiness + name-Nodup invariants.
  · `resolve   : Resolve.Table objects.val.size` — per-undef-ref
                 resolution outcome. `ofObjects` rejects when a
                 `strongUndef` remains.
  · `layout      : Layout objects.val.size` — page math, per-elf
                 advance + cumulative span, plus per-segment
                 invariants (`pageEnd_lt` etc.).
  · `initOrder : Array (Fin objects.val.size)` — DFS post-order
                 init sequence over the dep DAG.

Every contained index (`SymRef`, `RelocEntry.target`, `initOrder`,
the per-elf `bases` computed later) is typed at the same `n`, so
consumers (`Materialize.build`, `Materialize.ctorAddrs`) thread one
object instead of parallel arrays + coherence proofs.

`Plan.ofObjects` is the single fallible construction:
  1. Build the resolve table; reject if any strong undef remains.
  2. Plan every elf's segments and relocations (`Layout.ofElfs`).
     This is where `SegmentLayout`'s per-segment invariants are
     discharged and `ElfLayout.segmentsSorted` is validated.
  3. Compute the DFS post-order init sequence.

The IO bookend (`Main.load` / `Main.debug`) calls `Plan.ofObjects`
once, wraps the result in a `Materialize.BasedPlan` together with
the IO-supplied `Reserve`, and passes that down to materialize.
-/

import LeanLoad.Discover.Plan
import LeanLoad.Plan.Layout
import LeanLoad.Plan.Resolve
import LeanLoad.Plan.Init

namespace LeanLoad.Plan

open LeanLoad
open LeanLoad.Discover (ObjectList)
open LeanLoad.Elaborate (Elf)

/-- The unified pure-pipeline aggregate. Every sub-output is indexed
    by `objects.val.size`, so consumers can index `lp.elfs`,
    `bases`, and per-rela `SymRef.objectIdx` totally without size-
    coherence proofs at every call site. -/
structure Plan where
  /-- Discovered objects (main + transitive deps), in BFS order. -/
  objects   : ObjectList
  /-- Per-undef-reference resolution outcome. `Plan.ofObjects`
      rejects when any entry is `strongUndef`. -/
  resolve   : Resolve.Table objects.val.size
  /-- Page math + per-segment relocations, with `elfs_size` tying
      `layout.elfs` to the object count. -/
  layout      : Layout objects.val.size
  /-- DFS post-order over the dep DAG; `Fin n` typed so
      `Materialize.initAddrs` indexes `layout.elfs` and `bases`
      totally. -/
  initOrder : Array (Fin objects.val.size)

namespace Plan

/-- Project the elf array of the bundled object list — convenience
    for `Materialize.build` (which needs `Array Elf` parallel to
    `layout.elfs` for `bakeSegmentRelocs`). The size lemma
    `objectElfs_size` says it has size `objects.val.size`. -/
def objectElfs (p : Plan) : Array Elf :=
  p.objects.val.map (·.elf)

theorem objectElfs_size (p : Plan) :
    p.objectElfs.size = p.objects.val.size := by
  unfold objectElfs; simp

/-- Per-arch relocation formula, picked off the main elf's
    `e_machine`. -/
def formula (p : Plan) : Elaborate.Formula :=
  Elaborate.formulaFor p.objects.main.elf.machine

/-- Build a `Plan` from a discovered object list. Fails with a typed
    error if:
      • any strong undef remains unresolved, or
      • `Layout.ofElfs` rejects the layout (page-aligned overlap or
        UInt64 cumulative-span overflow). -/
def ofObjects (objs : ObjectList) : Except String Plan := do
  let elfs := objs.val.map (·.elf)
  have h_size : elfs.size = objs.val.size := by simp [elfs]
  -- Sized variants thread `h_size` through their construction so the
  -- result types are already at `objs.val.size` — no outer `▸` cast.
  let resolve := Resolve.buildTableSized elfs h_size
  -- Reject loads with strong-undef references — production loaders
  -- would surface this as an early `ld.so` failure.
  if let some u := resolve.missing[0]? then
    .error s!"Plan.ofObjects: {resolve.missing.size} unresolved strong symbol(s); \
      first: {u.name}"
  let layout ← Layout.ofElfsSized elfs h_size resolve
  let initOrder := Init.order objs
  return { objects := objs, resolve, layout, initOrder }

end Plan

end LeanLoad.Plan

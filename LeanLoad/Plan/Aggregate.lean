/-
Top-level pure-pipeline aggregate.

An `Aggregate` bundles the four base-free planner outputs under one
structure parameterised by the object count `graph.objects.size`:

  · `graph     : LoadGraph` — main + transitive deps in BFS order.
                 Carries non-emptiness + name-Nodup + dep invariants.
  · `resolve   : Resolve.Table graph.objects.size` — per-undef-ref
                 resolution outcome. `ofGraph` rejects when a
                 `strongUndef` remains.
  · `layout    : Layout graph.objects.size` — page math, per-elf
                 advance + cumulative span, plus per-segment
                 invariants (`pageEnd_lt` etc.).
  · `initOrder : Array (Fin graph.objects.size)` — DFS post-order
                 init sequence over the dep DAG.

Every contained index (`SymRef`, `Entry.target`, `initOrder`,
the per-elf `bases` computed later) is typed at the same `objCount`, so
consumers (`Materialize.build`, `Materialize.ctorAddrs`) thread one
object instead of parallel arrays + coherence proofs.

`Aggregate.ofGraph` is the single fallible construction:
  1. Build the resolve table; reject if any strong undef remains.
  2. Plan every elf's segments and relocations (`Layout.ofElfs`).
     This is where `SegmentLayout`'s per-segment invariants are
     discharged and `ElfLayout.segmentsSorted` is validated.
  3. Compute the DFS post-order init sequence.

The IO bookend (`Main.load` / `Main.debug`) calls `Aggregate.ofGraph`
once, wraps the result in a `Materialize.BoundPlan` together with
the IO-supplied `Reserve`, and passes that down to materialize.
-/

import LeanLoad.Discover.Step
import LeanLoad.Plan.Layout
import LeanLoad.Plan.Resolve
import LeanLoad.Plan.Init

namespace LeanLoad.Plan

open LeanLoad
open LeanLoad.Discover (LoadGraph)
open LeanLoad.Elaborate (Elf)

/-- The unified pure-pipeline aggregate. Every sub-output is indexed
    by `graph.objects.size`, so consumers can index `lp.elfs`,
    `bases`, and per-rela `SymRef.objectIdx` totally without size-
    coherence proofs at every call site. -/
structure Aggregate where
  /-- Discovered objects + dep edges (the BFS-built dependency graph). -/
  graph     : LoadGraph
  /-- Per-undef-reference resolution outcome. `Aggregate.ofGraph`
      rejects when any entry is `strongUndef`. -/
  resolve   : Resolve.Table graph.objects.size
  /-- Page math + per-segment relocations, with `elfs_size` tying
      `layout.elfs` to the object count. -/
  layout    : Layout graph.objects.size
  /-- DFS post-order over the dep DAG; `Fin objCount` typed so
      `Materialize.initAddrs` indexes `layout.elfs` and `bases`
      totally. -/
  initOrder : Array (Fin graph.objects.size)

namespace Aggregate

/-- Project the elf array of the bundled object list — convenience
    for `Materialize.build` (which needs `Array Elf` parallel to
    `layout.elfs` for `bakeSegmentRelocs`). The size lemma
    `objectElfs_size` says it has size `graph.objects.size`. -/
def objectElfs (p : Aggregate) : Array Elf :=
  p.graph.objects.map (·.elf)

theorem objectElfs_size (p : Aggregate) :
    p.objectElfs.size = p.graph.objects.size := by
  unfold objectElfs; simp

/-- Per-arch relocation formula, picked off the main elf's
    `e_machine`. -/
def formula (p : Aggregate) : Elaborate.Formula :=
  Elaborate.formulaFor p.graph.main.elf.machine

/-- Build an `Aggregate` from a `LoadGraph`. Fails with a typed
    error if:
      • any strong undef remains unresolved, or
      • `Layout.ofElfs` rejects the layout (page-aligned overlap or
        UInt64 cumulative-span overflow). -/
def ofGraph (g : LoadGraph) : Except String Aggregate := do
  let elfs := g.objects.map (·.elf)
  have h_size : elfs.size = g.objects.size := by simp [elfs]
  -- The optional `h_size` argument retypes the result at
  -- `g.objects.size` (instead of `elfs.size`) — no outer `▸` cast needed.
  let resolve := Resolve.buildTable elfs h_size
  -- Reject loads with strong-undef references — production loaders
  -- would surface this as an early `ld.so` failure.
  if let some u := resolve.missing[0]? then
    .error s!"Aggregate.ofGraph: {resolve.missing.size} unresolved strong symbol(s); \
      first: {u.name}"
  let layout ← Layout.ofElfs elfs resolve h_size
  let initOrder := Init.order g
  return { graph := g, resolve, layout, initOrder }

end Aggregate

end LeanLoad.Plan

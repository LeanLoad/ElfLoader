/-
Top-level pure-pipeline aggregate.

A `Plan` bundles the four base-free planner outputs — `Discover`'s
`ObjectList`, `Resolve.Table`, `LoadPlan`, and `Init.order` — under
one structure parameterised by the object count `objects.val.size`.
Every contained index (`SymRef`, `RelocEntry.target`, `initOrder`,
`bases`) is typed at the same `n`, so consumers (`Materialize.build`,
`Materialize.initAddrs`) thread a single object instead of a fan of
parallel arrays + coherence proofs.

`Plan.ofObjects` is the single fallible construction:
  • Builds the resolve table; rejects when strong undef remains.
  • Plans every elf's segments and relocations (`LoadPlan.ofElfs`).
  • Computes the DFS post-order init sequence.

The IO bookend (`Main.load` / `Main.debug`) calls `Plan.ofObjects`
once and then passes the whole `Plan` to materialize / debug print.
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
      `load.elfs` to the object count. -/
  load      : LoadPlan objects.val.size
  /-- DFS post-order over the dep DAG; `Fin n` typed so
      `Materialize.initAddrs` indexes `load.elfs` and `bases`
      totally. -/
  initOrder : Array (Fin objects.val.size)

namespace Plan

/-- Project the elf array of the bundled object list — convenience
    for `Materialize.build` (which needs `Array Elf` parallel to
    `load.elfs`). The size lemma `objects_elfs_size` says it has
    size `objects.val.size`. -/
def objectElfs (p : Plan) : Array Elf :=
  p.objects.val.map (·.elf)

theorem objectElfs_size (p : Plan) :
    p.objectElfs.size = p.objects.val.size := by
  unfold objectElfs; simp

/-- Project the file-handle array of the bundled object list. -/
def objectHandles (p : Plan) : Array Runtime.FileHandle :=
  p.objects.val.map (·.handle)

theorem objectHandles_size (p : Plan) :
    p.objectHandles.size = p.objects.val.size := by
  unfold objectHandles; simp

/-- Per-arch relocation formula, picked off the main elf's
    `e_machine`. -/
def formula (p : Plan) : Elaborate.Formula :=
  Elaborate.formulaFor p.objects.main.elf.machine

/-- Build a `Plan` from a discovered object list. Fails with a typed
    error if:
      • any strong undef remains unresolved, or
      • `LoadPlan.ofElfs` rejects the layout (page-aligned overlap or
        UInt64 cumulative-span overflow). -/
def ofObjects (objs : ObjectList) : Except String Plan := do
  let elfs := objs.val.map (·.elf)
  have h_eq : elfs.size = objs.val.size := by simp [elfs]
  let resolveRaw : Resolve.Table elfs.size := Resolve.buildTable elfs
  -- Reject loads with strong-undef references — production loaders
  -- would surface this as an early `ld.so` failure.
  if let some u := resolveRaw.missing[0]? then
    .error s!"Plan.ofObjects: {resolveRaw.missing.size} unresolved strong symbol(s); \
      first: {u.name}"
  let loadRaw ← LoadPlan.ofElfs elfs resolveRaw
  -- Cast everything from `elfs.size` to `objs.val.size` (provably
  -- equal). The cast is `Eq.symm`-direction since we want the
  -- type-parameter to read `objs.val.size`, the canonical anchor.
  let resolve : Resolve.Table objs.val.size := h_eq ▸ resolveRaw
  let load    : LoadPlan objs.val.size       := h_eq ▸ loadRaw
  let initOrder : Array (Fin objs.val.size)  := Init.order objs
  return { objects := objs, resolve, load, initOrder }

end Plan

end LeanLoad.Plan

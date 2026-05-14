/-
Init planner — base-free.

Produces a topological order over the discovered dep graph. gabi 08
mandates a *partial order* — "deps before dependents", cycle order
undefined. DFS post-order is *our* implementation choice (matches
glibc / musl); any valid topological sort would be conformant.
Reverse-BFS is *not* a valid topological sort on non-tree DAGs and
would violate the spec.

The dep edges live on `LoadGraph.deps` — recorded by Discover BFS at
edge-creation time, so the canonical-name dedup that converts
`DT_NEEDED libfoo.so` → loaded `libfoo.so.1` cannot drop edges
silently. `Init.order` just projects them and runs DFS post-order.

`order : (g : LoadGraph) → Array (Fin g.objects.size)` returns
Fin-indexed object indices so downstream consumers
(`Materialize.initAddrs`) can index `lp.elfs` and `bases` totally,
without `[]?`. The `Fin objCount` bound is preserved structurally through
DFS via the internal `DfsState objCount` carrier.

Address resolution (turn the order + bases + initArr into the flat
`Array UInt64` of ctor addresses to call) is base-aware and lives in
`Materialize.initAddrs`.
-/

import LeanLoad.Discover.Step
import LeanLoad.Elaborate.Elf

namespace LeanLoad.Plan.Init

open LeanLoad
open LeanLoad.Discover

-- ============================================================================
-- DFS post-order.
--
-- The `Fin objCount` bound on the produced order is preserved by carrying
-- `visited` and `order` in a `DfsState objCount` struct: every `push` into
-- `order` is guarded by `idx < objCount`, and `Array.set` preserves the
-- `visited.size = objCount` field.
-- ============================================================================

/-- DFS carrier. Keeps the visited bitmap (sized to `objCount`) alongside
    the partial order. -/
private structure DfsState (objCount : Nat) where
  visited     : Array Bool
  visitedSize : visited.size = objCount
  order       : Array (Fin objCount)

/-- Depth-first traversal helper. `visited[i]` marks an object that
    has either been emitted (`order` already contains it) or is
    currently in the descent path (cycle protection).

    `fuel` bounds the recursion depth. The caller seeds it with `objCount`
    (object count); each recursive call descends through one
    not-yet-visited object, so the bound is tight. With fuel, no
    `partial def` — `dfs` is structurally recursive. -/
private def dfs (fuel : Nat) (deps : Array (Array Nat)) (idx : Nat)
    (s : DfsState objCount) : DfsState objCount :=
  match fuel with
  | 0 => s
  | fuel + 1 =>
    if h : idx < objCount then
      have h_in : idx < s.visited.size := by rw [s.visitedSize]; exact h
      if s.visited[idx]'h_in then s
      else
        let v' := s.visited.set idx true
        let s' : DfsState objCount :=
          { visited := v'
            visitedSize := by
              show (s.visited.set idx true).size = objCount
              rw [Array.size_set]; exact s.visitedSize
            order := s.order }
        let children := (deps[idx]?).getD #[]
        let s'' := children.foldl (init := s') (fun st c => dfs fuel deps c st)
        { s'' with order := s''.order.push ⟨idx, h⟩ }
    else s
termination_by fuel

/-- Dependency order: depth-first post-order over `deps` from object 0
    (main). Init walks the result forward; fini walks it reversed. -/
def computeOrder (deps : Array (Array Nat)) (objCount : Nat) : Array (Fin objCount) :=
  if objCount == 0 then #[]
  else
    let s : DfsState objCount :=
      { visited := Array.replicate objCount false
        visitedSize := by simp
        order := Array.mkEmpty objCount }
    (dfs objCount deps 0 s).order

/-- Init order over an `LoadGraph`: project the BFS-recorded
    `g.deps` and run DFS post-order. The returned indices are typed
    `Fin g.objects.size` so downstream consumers can index `lp.elfs` /
    `bases` totally. -/
def order (g : LoadGraph) : Array (Fin g.objects.size) :=
  computeOrder g.deps g.objects.size

section Example
-- Three-object DAG: 0 (main) → {1, 2}; 1 → {2}; 2 → ∅.
-- DFS from 0 visits 1 first, descends to 2, emits 2 then 1, then
-- returns and emits 0. Result: deps before dependents, main last.
#guard (computeOrder #[#[1, 2], #[2], #[]] 3).map (·.val) = #[2, 1, 0]

-- Empty graph → empty order.
#guard (computeOrder #[] 0).map (·.val) = #[]

-- Linear chain 0 → 1 → 2 → 3: deeper objects emit first.
#guard (computeOrder #[#[1], #[2], #[3], #[]] 4).map (·.val) = #[3, 2, 1, 0]

-- Cycle 0 → 1 → 0: visited-flag breaks the back-edge mid-descent;
-- both still emit (gabi 08 leaves cycle order undefined — we just
-- terminate without re-recursing).
#guard (computeOrder #[#[1], #[0]] 2).map (·.val) = #[1, 0]

-- Diamond: 0 → {1, 2}; 1 → {3}; 2 → {3}; 3 → ∅.
-- 3 is shared by 1 and 2 — DFS emits it once on the first visit.
#guard (computeOrder #[#[1, 2], #[3], #[3], #[]] 4).map (·.val) = #[3, 1, 2, 0]
end Example

end LeanLoad.Plan.Init

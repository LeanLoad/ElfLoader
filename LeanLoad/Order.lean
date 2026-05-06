/-
Dependency order — pure.

Spec: gabi 08 § Initialization and Termination Functions.

> Before the initialization functions for any object A is called,
> the initialization functions for any other objects that object A
> depends on are called. … The order of initialization for circular
> dependencies is undefined.

DFS post-order over the `DT_NEEDED` graph; cycles broken by a
visited set; total via fuel. Output is an `Array Nat` of
`DepGraph.objects` indices. Init runs them in order; fini runs the
reverse (`g.order.reverse`).
-/

import LeanLoad.DiscoverPlan
import LeanLoad.Fixtures

namespace LeanLoad.Order

open LeanLoad
open LeanLoad.Discover

/-- Depth-first traversal helper. `visited[i]` marks an object that
    has either been emitted (`order` already contains it) or is
    currently in the descent path (cycle protection).

    `fuel` bounds the recursion depth. The caller seeds it with
    `g.objects.size`; each recursive call descends through one
    not-yet-visited object, so the bound is tight. With fuel, no
    `partial def` — `dfs` is structurally recursive.

    Pure-recursive form: the inner `for childIdx in childIdxs` is
    `Array.foldl` over `(visited, order)`, threading both as the
    fold accumulator. Lifts directly under `Array.foldl_induction`
    in `LeanLoad.Thm.Order`. Public (not `private`) so the theorem
    file can quantify over its result. -/
def dfs (fuel : Nat) (g : DepGraph) (idx : Nat)
    (visited : Array Bool) (order : Array Nat) : Array Bool × Array Nat :=
  match fuel with
  | 0 => (visited, order)
  | fuel + 1 =>
    if h : idx < visited.size then
      if visited[idx] then (visited, order)
      else
        let visited := visited.set idx true
        let children := (g.deps[idx]?).getD #[]
        let (v, o) := children.foldl (init := (visited, order))
                        (fun st c => dfs fuel g c st.1 st.2)
        (v, o.push idx)
    else (visited, order)
termination_by fuel

end LeanLoad.Order

namespace LeanLoad.Discover.DepGraph

open LeanLoad.Order

/-- Dependency order: depth-first post-order over `DT_NEEDED` from
    object 0 (main). Init runs `g.order` forward; fini runs
    `g.order.reverse`. -/
def order (g : DepGraph) : Array Nat :=
  let n := g.objects.size
  if n == 0 then #[]
  else
    let visited := Array.replicate n false
    let acc : Array Nat := Array.mkEmpty n
    (dfs n g 0 visited acc).snd

end LeanLoad.Discover.DepGraph

namespace LeanLoad.Order

open LeanLoad
open LeanLoad.Discover

-- ============================================================================
-- Compile-time unit tests on synthetic dep graphs (`synthDepGraph`
-- from `LeanLoad.Fixtures`).
-- ============================================================================
section UnitTest
open LeanLoad.Fixtures

private def emptyG   : DepGraph := synthDepGraph #[]
private def loneG    : DepGraph := synthDepGraph #[synthObj "main"]
private def chainG   : DepGraph := synthDepGraph #[
  synthObj "main"      (needed := #["libfoo.so"]),
  synthObj "libfoo.so" (needed := #["libbar.so"]),
  synthObj "libbar.so"
]
/-- Diamond: main needs libfoo + libbar; both need libcommon (visited
    once). Post-order = `[3, 1, 2, 0]`. -/
private def diamondG : DepGraph := synthDepGraph #[
  synthObj "main"         (needed := #["libfoo.so", "libbar.so"]),
  synthObj "libfoo.so"    (needed := #["libcommon.so"]),
  synthObj "libbar.so"    (needed := #["libcommon.so"]),
  synthObj "libcommon.so"
]
/-- Cycle libA ↔ libB. Order is implementation-defined (gabi 08 says
    "undefined for circular dependencies") — we just check the visited
    set terminates and emits every node exactly once. -/
private def cycleG : DepGraph := synthDepGraph #[
  synthObj "main"    (needed := #["libA.so"]),
  synthObj "libA.so" (needed := #["libB.so"]),
  synthObj "libB.so" (needed := #["libA.so"])
]

#guard emptyG.order         = #[]
#guard emptyG.order.reverse = #[]
#guard loneG.order          = #[0]
#guard chainG.order         = #[2, 1, 0]
#guard chainG.order.reverse = #[0, 1, 2]
#guard diamondG.order       = #[3, 1, 2, 0]
#guard cycleG.order.size    = 3

end UnitTest

end LeanLoad.Order

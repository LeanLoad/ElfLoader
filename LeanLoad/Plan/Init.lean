/-
Initialization and termination ordering.

Spec: gabi 08 § Initialization and Termination Functions.

> Before the initialization functions for any object A is called, the
> initialization functions for any other objects that object A depends
> on are called. … The order of initialization for circular
> dependencies is undefined.

We compute init order by depth-first traversal from main, recursing
into each `DT_NEEDED` before emitting the current object — i.e.,
post-order. Cycles are broken by a "visited" set: once we start
visiting an object we mark it; if a recursive descent meets it again,
we skip. Termination order is the reverse.

Output: `Array Nat` of `LinkMap.objects` indices. Init runs them
in order; fini runs them in reverse.
-/

import LeanLoad.Discover
import LeanLoad.TestFixture

namespace LeanLoad.Plan.Init

open LeanLoad

/-- Find the index of an object whose `name` matches one of `nameOrSoname`.
    Used to follow `DT_NEEDED` strings to their loaded objects. -/
private def findObject (lm : Discover.LinkMap) (name : String) : Option Nat :=
  lm.objects.findIdx? (·.name == name)

/-- Depth-first traversal helper. `visited[i]` marks an object that
    has either been emitted (`order` already contains it) or is
    currently in the descent path (cycle protection).

    `fuel` bounds the recursion depth and lets Lean mechanically
    discharge termination. The caller (`initOrder`) seeds it with
    `lm.objects.size`, which is sufficient because each recursive
    call descends through one not-yet-visited object, and there are
    at most `lm.objects.size` of those. With this, no `partial def`
    is needed — `dfs` is structurally recursive on `fuel`. -/
private def dfs (fuel : Nat) (lm : Discover.LinkMap)
    (idx : Nat) (visited : Array Bool) (order : Array Nat) : Array Bool × Array Nat :=
  match fuel with
  | 0 => (visited, order)
  | fuel + 1 => Id.run do
    if h : idx < visited.size then
      if visited[idx] then return (visited, order)
    else
      return (visited, order)
    let mut visited := visited.set! idx true
    let mut order := order
    let some obj := lm.objects[idx]? | return (visited, order)
    for needed in obj.elf.needed do
      if let some childIdx := findObject lm needed then
        let (v', o') := dfs fuel lm childIdx visited order
        visited := v'
        order := o'
    order := order.push idx
    return (visited, order)
termination_by fuel

/-- Compute init order: depth-first post-order from object 0 (main).
    Result is an array of object indices to invoke in sequence. -/
def initOrder (lm : Discover.LinkMap) : Array Nat :=
  let n := lm.objects.size
  if n == 0 then #[]
  else
    let visited := Array.replicate n false
    let order : Array Nat := Array.mkEmpty n
    (dfs n lm 0 visited order).snd

/-- Termination order (`DT_FINI_ARRAY`, `DT_FINI`). Reverse of init. -/
def finiOrder (lm : Discover.LinkMap) : Array Nat :=
  (initOrder lm).reverse

-- ============================================================================
-- Compile-time unit tests on synthetic link maps (`synthObj` from
-- `LeanLoad.TestFixture`).
-- ============================================================================
section UnitTest
open LeanLoad.Test

private def emptyLM   : Discover.LinkMap := { objects := #[] }
private def loneLM    : Discover.LinkMap := { objects := #[synthObj "main"] }
private def chainLM   : Discover.LinkMap := { objects := #[
  synthObj "main"      (needed := #["libfoo.so"]),
  synthObj "libfoo.so" (needed := #["libbar.so"]),
  synthObj "libbar.so"
] }
/-- Diamond: main needs libfoo + libbar; both need libcommon (visited
    once). Post-order = `[3, 1, 2, 0]`. -/
private def diamondLM : Discover.LinkMap := { objects := #[
  synthObj "main"         (needed := #["libfoo.so", "libbar.so"]),
  synthObj "libfoo.so"    (needed := #["libcommon.so"]),
  synthObj "libbar.so"    (needed := #["libcommon.so"]),
  synthObj "libcommon.so"
] }
/-- Cycle libA ↔ libB. Order is implementation-defined (gabi 08 says
    "undefined for circular dependencies") — we just check the visited
    set terminates and emits every node exactly once. -/
private def cycleLM   : Discover.LinkMap := { objects := #[
  synthObj "main"    (needed := #["libA.so"]),
  synthObj "libA.so" (needed := #["libB.so"]),
  synthObj "libB.so" (needed := #["libA.so"])
] }

#guard initOrder emptyLM   = #[]
#guard finiOrder emptyLM   = #[]
#guard initOrder loneLM    = #[0]
#guard initOrder chainLM   = #[2, 1, 0]
#guard finiOrder chainLM   = #[0, 1, 2]
#guard initOrder diamondLM = #[3, 1, 2, 0]
#guard (initOrder cycleLM).size = 3

end UnitTest

end LeanLoad.Plan.Init

-- ============================================================================
-- Tests.
-- ============================================================================
namespace LeanLoad.Plan.Init.Test

/-- Init order: post-order DFS. Main (idx 0) is the root, so it must
    appear last (after all of its transitive deps). -/
def run (lm : LeanLoad.Discover.LinkMap) : IO Nat := do
  let mut failures := 0
  let order := LeanLoad.Plan.Init.initOrder lm
  if order.size != lm.objects.size then
    IO.eprintln s!"init order size {order.size} ≠ object count {lm.objects.size}"
    failures := failures + 1
  if order.back? != some 0 then
    IO.eprintln s!"main (idx 0) should be last in init order; got {order}"
    failures := failures + 1
  return failures

end LeanLoad.Plan.Init.Test

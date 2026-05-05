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

Output: `Array Nat` of `Closure.objects` indices. Init runs them
in order; fini runs them in reverse.
-/

import LeanLoad.Discover

namespace LeanLoad.Link.Init

open LeanLoad

/-- Find the index of an object whose `name` matches one of `nameOrSoname`.
    Used to follow `DT_NEEDED` strings to their loaded objects. -/
private def findObject (li : Discover.Closure) (name : String) : Option Nat :=
  li.objects.findIdx? (·.name == name)

/-- Depth-first traversal helper. `visited[i]` marks an object that
    has either been emitted (`order` already contains it) or is
    currently in the descent path (cycle protection). -/
private partial def dfs (li : Discover.Closure)
    (idx : Nat) (visited : Array Bool) (order : Array Nat) : Array Bool × Array Nat := Id.run do
  if h : idx < visited.size then
    if visited[idx] then return (visited, order)
  else
    return (visited, order)
  let mut visited := visited.set! idx true
  let mut order := order
  let some obj := li.objects[idx]? | return (visited, order)
  for needed in obj.elf.needed do
    if let some childIdx := findObject li needed then
      let (v', o') := dfs li childIdx visited order
      visited := v'
      order := o'
  order := order.push idx
  return (visited, order)

/-- Compute init order: depth-first post-order from object 0 (main).
    Result is an array of object indices to invoke in sequence. -/
def initOrder (li : Discover.Closure) : Array Nat :=
  let n := li.objects.size
  if n == 0 then #[]
  else
    let visited := Array.replicate n false
    let order : Array Nat := Array.mkEmpty n
    (dfs li 0 visited order).snd

/-- Termination order (`DT_FINI_ARRAY`, `DT_FINI`). Reverse of init. -/
def finiOrder (li : Discover.Closure) : Array Nat :=
  (initOrder li).reverse

end LeanLoad.Link.Init

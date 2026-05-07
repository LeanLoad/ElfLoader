/-
Init planner — pure.

Produces the list of constructor addresses to call, in the order
gabi 08 § Initialization and Termination Functions requires. The
trusted IO executor (`Exec.runInits`) just iterates the result.

Two pieces here:

  1. Topological sort over the discovered dep graph. gabi 08 mandates
     a *partial order* — "deps before dependents", cycle order
     undefined. DFS post-order is *our* implementation choice (matches
     glibc / musl); any valid topological sort would be conformant.
     Reverse-BFS is *not* a valid topological sort on non-tree DAGs
     and would violate the spec.

  2. Address resolution. For each object in the order, walk
     `elf.initArr`. ET_DYN entries are relative addresses (gabi 07
     § Base Address) and need the chosen base added; ET_EXEC entries
     are already absolute. Filter zero entries.

The dep edges are re-derived here from `obj.elf.needed` rather than
stored in `ObjectList` — `Discover`'s job is the BFS, not init order.
-/

import LeanLoad.Plan.Discover
import LeanLoad.Plan.Layout
import LeanLoad.Elaborate.Elf
import Std.Data.HashMap

namespace LeanLoad.Init

open LeanLoad
open LeanLoad.Discover
open LeanLoad.Layout

-- ============================================================================
-- Dep edges (re-derived from `obj.elf.needed`)
-- ============================================================================

/-- Resolve each object's `DT_NEEDED` strings to indices in `objects`.
    Builds a `name → index` map once (O(N)) so each lookup is O(1) on
    average; total O(N + total NEEDED entries).

    Names in a well-formed `ObjectList` are unique (the BFS dedups via
    `alreadyLoaded`), so the map insertion order is irrelevant. A
    `NEEDED` string with no matching object is silently dropped — the
    BFS would only have failed to resolve it if we'd ignored a hard
    error upstream, which `discover` doesn't. -/
def buildDeps (objects : Array LoadedObject) : Array (Array Nat) :=
  let nameToIdx : Std.HashMap String Nat := Id.run do
    let mut m : Std.HashMap String Nat := ∅
    for h : i in [:objects.size] do
      m := m.insert objects[i].name i
    return m
  objects.map fun obj =>
    obj.elf.needed.filterMap nameToIdx.get?

-- ============================================================================
-- DFS post-order
-- ============================================================================

/-- Depth-first traversal helper. `visited[i]` marks an object that
    has either been emitted (`order` already contains it) or is
    currently in the descent path (cycle protection).

    `fuel` bounds the recursion depth. The caller seeds it with `n`
    (object count); each recursive call descends through one
    not-yet-visited object, so the bound is tight. With fuel, no
    `partial def` — `dfs` is structurally recursive. -/
def dfs (fuel : Nat) (deps : Array (Array Nat)) (idx : Nat)
    (visited : Array Bool) (order : Array Nat) : Array Bool × Array Nat :=
  match fuel with
  | 0 => (visited, order)
  | fuel + 1 =>
    if h : idx < visited.size then
      if visited[idx] then (visited, order)
      else
        let visited := visited.set idx true
        let children := (deps[idx]?).getD #[]
        let (v, o) := children.foldl (init := (visited, order))
                        (fun st c => dfs fuel deps c st.1 st.2)
        (v, o.push idx)
    else (visited, order)
termination_by fuel

/-- Dependency order: depth-first post-order over `deps` from object 0
    (main). Init walks the result forward; fini walks it reversed. -/
def computeOrder (deps : Array (Array Nat)) (n : Nat) : Array Nat :=
  if n == 0 then #[]
  else
    let visited := Array.replicate n false
    let acc : Array Nat := Array.mkEmpty n
    (dfs n deps 0 visited acc).snd

/-- Init order over a `ObjectList`: builds dep edges, runs DFS
    post-order. Convenience wrapper used by `plan` and the debug
    printer. -/
def order (g : ObjectList) : Array Nat :=
  computeOrder (buildDeps g.val) g.val.size

section Example
-- Three-object DAG: 0 (main) → {1, 2}; 1 → {2}; 2 → ∅.
-- DFS from 0 visits 1 first, descends to 2, emits 2 then 1, then
-- returns and emits 0. Result: deps before dependents, main last.
#guard computeOrder #[#[1, 2], #[2], #[]] 3 = #[2, 1, 0]

-- Empty graph → empty order.
#guard computeOrder #[] 0 = #[]

-- Linear chain 0 → 1 → 2 → 3: deeper objects emit first.
#guard computeOrder #[#[1], #[2], #[3], #[]] 4 = #[3, 2, 1, 0]

-- Cycle 0 → 1 → 0: visited-flag breaks the back-edge mid-descent;
-- both still emit (gabi 08 leaves cycle order undefined — we just
-- terminate without re-recursing).
#guard computeOrder #[#[1], #[0]] 2 = #[1, 0]

-- Diamond: 0 → {1, 2}; 1 → {3}; 2 → {3}; 3 → ∅.
-- 3 is shared by 1 and 2 — DFS emits it once on the first visit.
#guard computeOrder #[#[1, 2], #[3], #[3], #[]] 4 = #[3, 1, 2, 0]
end Example

-- ============================================================================
-- Address resolution
-- ============================================================================

/-- Constructor function addresses to call, in init order. Walks
    `order` forward (init); fini callers walk `(plan g layouts order).reverse`.

    For each object, walks `elf.initArr`: ET_DYN entries are relative
    (add base); ET_EXEC are absolute. Zero entries are skipped — gabi
    leaves them unspecified, but historical practice (and the table
    layout where zero-terminators are common) treats them as no-ops.

    Pure: takes `layouts` (per-object base + segments) directly, not
    a `ProcessImage`. The base is the only thing this function needs
    from the post-Map state, and bases come from Layout deterministically.
    Threading layouts instead of an image keeps Init.plan free of any
    IO dependency. -/
def plan (g : ObjectList) (layouts : Array ObjectLayout)
    (order : Array Nat) : Array UInt64 := Id.run do
  let mut addrs : Array UInt64 := #[]
  for objectIdx in order do
    let some obj := g.val[objectIdx]?  | continue
    let some lyt := layouts[objectIdx]? | continue
    let isExec := obj.elf.elfType == .exec
    for entry in obj.elf.initArr do
      let fnAddr := if isExec then entry else lyt.base + entry
      if fnAddr != 0 then addrs := addrs.push fnAddr
  return addrs

end LeanLoad.Init

/-
Discover work items and resolver output.

`WorkItem` is the explicit unit of pending dependency discovery: a raw
`DT_NEEDED` string plus the referring object's `DT_RUNPATH`. A
`ResolvedObject` is what a resolver returns after path search, open, and
checked parse, with the canonical dedup key already chosen.
-/

import LeanLoad.Parse
import LeanLoad.Runtime

namespace LeanLoad.Discover

open LeanLoad

/-- One dependency request to resolve next. `needed` is the raw `DT_NEEDED`
    string from the referring object; `runpath` is that object's
    `DT_RUNPATH`, if present. This keeps the traversal's pending work
    explicit instead of passing loose strings around. -/
structure WorkItem where
  needed  : String
  runpath : Option String
  deriving Repr

namespace WorkItem

/-- Build the work items created by one object's `DT_NEEDED` array. -/
def ofNeededArray (runpath : Option String) (needed : Array String) :
    List WorkItem :=
  needed.toList.map (fun name => { needed := name, runpath })

end WorkItem

/-- A resolved dependency, ready to insert into the discovered set. `name`
    is the canonical dedup key (`DT_SONAME` in production). -/
structure ResolvedObject where
  name   : String
  handle : Runtime.File
  elf    : LeanLoad.Parse.Elf
  deriving Repr

end LeanLoad.Discover

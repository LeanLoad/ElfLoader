/-
Init: invoke each loaded object's `DT_INIT_ARRAY` constructors,
in the order computed by `Plan.Init.initOrder`.

Spec: gabi 08 § Initialization and Termination Functions. ET_DYN
entries are relative addresses (gabi 07 § Base Address) and need the
chosen base added; ET_EXEC entries are already absolute.
-/

import LeanLoad.Discover
import LeanLoad.Plan.Reloc
import LeanLoad.Plan.Layout
import LeanLoad.FFI.Exec

namespace LeanLoad.Load

open LeanLoad.FFI

/-- Call every entry of one object's `DT_INIT_ARRAY`. -/
def runObjectInits (lm : Discover.LinkMap) (bases : Plan.Reloc.Bases)
    (objectIdx : Nat) : IO Unit := do
  let some obj := lm.objects[objectIdx]? | return ()
  let some base := bases[objectIdx]? | return ()
  let isExec := obj.elf.header.e_type = 2
  for entry in obj.elf.initArr do
    let fnAddr := if isExec then entry else base + entry
    if fnAddr != 0 then Exec.callCtor fnAddr

/-- Call constructors for every object in `initOrder`, including main. -/
def runInits (lm : Discover.LinkMap) (bases : Plan.Reloc.Bases)
    (plan : Plan.Layout.LoaderPlan) : IO Unit := do
  for objectIdx in plan.initOrder do
    runObjectInits lm bases objectIdx

end LeanLoad.Load

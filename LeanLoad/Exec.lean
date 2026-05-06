/-
Init / Exec stages: invoke each loaded object's constructors, then
build the kernel-style stack and hand control to the loaded image.

Spec: gabi 08 § Initialization and Termination Functions, gabi 08 §
Process Initialization. ET_DYN init-array entries are relative
addresses (gabi 07 § Base Address) and need the chosen base added;
ET_EXEC entries are already absolute. AT_PHDR / AT_PHENT / AT_PHNUM
/ AT_ENTRY in the auxv are required by the process-startup contract
(populated by `Runtime.execAndJump` in `runtime/exec.c`).
-/

import LeanLoad.Discover
import LeanLoad.Layout
import LeanLoad.Reloc
import LeanLoad.Runtime
import LeanLoad.Spec.Program

namespace LeanLoad.Load

open LeanLoad

-- ============================================================================
-- Init / fini invocation
-- ============================================================================

/-- Call every entry of one object's `DT_INIT_ARRAY`. -/
def runObjectInits (lm : Discover.LinkMap) (bases : Reloc.Bases)
    (objectIdx : Nat) : IO Unit := do
  let some obj := lm.objects[objectIdx]? | return ()
  let some base := bases[objectIdx]? | return ()
  let isExec := obj.elf.header.e_type = 2
  for entry in obj.elf.initArr do
    let fnAddr := if isExec then entry else base + entry
    if fnAddr != 0 then Runtime.callCtor fnAddr

/-- Call constructors for every object in `initOrder`, including main. -/
def runInits (lm : Discover.LinkMap) (bases : Reloc.Bases)
    (plan : Layout.Layout) : IO Unit := do
  for objectIdx in plan.initOrder do
    runObjectInits lm bases objectIdx

-- ============================================================================
-- Stack + jump (does not return)
-- ============================================================================

/-- Stack size for the loaded program. Matches musl's default (8 MiB). -/
def stackBytes : USize := 8 * 1024 * 1024

/-- Allocate kernel-style stack and jump to entry. **Does not return.** -/
def transferControl (mainObj : Discover.LoadedObject) (plan : Layout.Layout)
    (bases : Reloc.Bases) (path : String) : IO Unit := do
  let some mainLayout := plan.layouts[0]?
    | throw (IO.userError "load: empty plan")
  let some mainBase := bases[0]?
    | throw (IO.userError "load: missing main base")
  let stack ← Runtime.mmapStack stackBytes
  let entry  := mainBase + mainLayout.entry.getD 0
  let phdrVa := mainBase + mainObj.elf.header.e_phoff
  let phnum  := mainObj.elf.header.e_phnum.toUInt64
  let phent  := Spec.Program.entrySize.toUInt64
  Runtime.execAndJump entry phdrVa phent phnum 0 stack path

end LeanLoad.Load

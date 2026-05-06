/-
Exec stage: invoke each loaded object's constructors, then build the
kernel-style stack and hand control to the loaded image.

Spec: gabi 08 § Initialization and Termination Functions, gabi 08 §
Process Initialization. ET_DYN init-array entries are relative
addresses (gabi 07 § Base Address) and need the chosen base added;
ET_EXEC entries are already absolute. AT_PHDR / AT_PHENT / AT_PHNUM
/ AT_ENTRY in the auxv are required by the process-startup contract
(populated by `Runtime.execAndJump` in `runtime/exec.c`).
-/

import LeanLoad.Discover
import LeanLoad.Layout
import LeanLoad.Map
import LeanLoad.Reloc
import LeanLoad.Runtime
import LeanLoad.Spec.Program

namespace LeanLoad.Exec

open LeanLoad
open LeanLoad.Discover

-- ============================================================================
-- Init / fini invocation
-- ============================================================================

/-- Call constructors for every object in `order`, including main.
    Pass `g.order` (DFS post-order over deps); `runFini`, when added,
    will walk `g.order.reverse`. ET_DYN init-array entries are
    relative addresses and need the chosen base added; ET_EXEC
    entries are already absolute. -/
def runInits (g : DepGraph) (image : Map.ProcessImage) (order : Array Nat) : IO Unit := do
  for objectIdx in order do
    let some obj := g.objects[objectIdx]?     | continue
    let some lyt := image.layouts[objectIdx]? | continue
    let isExec := obj.elf.header.e_type = 2
    for entry in obj.elf.initArr do
      let fnAddr := if isExec then entry else lyt.base + entry
      if fnAddr != 0 then Runtime.callCtor fnAddr

-- ============================================================================
-- Stack + jump (does not return)
-- ============================================================================

/-- Stack size for the loaded program. Matches musl's default (8 MiB). -/
def stackBytes : USize := 8 * 1024 * 1024

/-- Allocate kernel-style stack and jump to entry. **Does not return.** -/
def transferControl (mainObj : Discover.LoadedObject) (image : Map.ProcessImage)
    (path : String) : IO Unit := do
  let some mainLayout := image.layouts[0]?
    | throw (IO.userError "load: empty layouts")
  let stack ← Runtime.mmapStack stackBytes
  let entry  := mainLayout.base + mainLayout.entry.getD 0
  let phdrVa := mainLayout.base + mainObj.elf.header.e_phoff
  let phnum  := mainObj.elf.header.e_phnum.toUInt64
  let phent  := Spec.Program.entrySize.toUInt64
  Runtime.execAndJump entry phdrVa phent phnum 0 stack path

end LeanLoad.Exec

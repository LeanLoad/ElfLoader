/-
Exec stage: call constructors and hand control to the loaded image.
The pure decisions (which ctor addresses, what stack contents, what
order) live in `LeanLoad.InitPlan`; this file owns the IO seam —
calling each ctor and the no-return `execAndJump`.

Spec: gabi 08 § Process Initialization. AT_PHDR / AT_PHENT /
AT_PHNUM / AT_ENTRY in the auxv are required by the process-startup
contract (populated by `Runtime.execAndJump` in `runtime/exec.c`).
-/

import LeanLoad.DiscoverPlan
import LeanLoad.Image
import LeanLoad.InitPlan
import LeanLoad.Layout
import LeanLoad.Runtime
import LeanLoad.Spec.Program

namespace LeanLoad.Exec

open LeanLoad
open LeanLoad.Discover

-- ============================================================================
-- Init: call each constructor address.
--
-- Formerly `LeanLoad.Init.apply` in `InitApply.lean`. Lives here
-- alongside `transferControl` because both are the trusted IO seam
-- after Map+Apply have prepared memory; splitting them across two
-- files added file count without separating concerns.
-- ============================================================================

/-- Call each constructor address in `addrs`. Init callers pass the
    result of `Init.plan` as-is; fini callers pass `(Init.plan ...).reverse`. -/
def runInits (rt : Runtime.Ops) (addrs : Array UInt64) : IO Unit :=
  addrs.forM rt.callCtor

-- ============================================================================
-- Stack + jump (does not return)
-- ============================================================================

/-- Stack size for the loaded program. Matches musl's default (8 MiB). -/
def stackBytes : USize := 8 * 1024 * 1024

/-- Allocate kernel-style stack and jump to entry. **Does not return.** -/
def transferControl {n : Nat} (rt : Runtime.Ops) (mainObj : Discover.LoadedObject)
    (image : Map.ProcessImage n) (path : String) : IO Unit := do
  let some mainImg := image.objects[0]?
    | throw (IO.userError "load: empty objects")
  let stack ← rt.mmapStack stackBytes
  let entry  := mainImg.layout.base + mainImg.layout.entry.getD 0
  let phdrVa := mainImg.layout.base + mainObj.elf.header.e_phoff
  let phnum  := mainObj.elf.header.e_phnum.toUInt64
  let phent  := Spec.Program.entrySize.toUInt64
  rt.execAndJump entry phdrVa phent phnum 0 stack path

end LeanLoad.Exec

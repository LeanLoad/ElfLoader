/-
Exec: build the kernel-style stack (argc/argv/envp/auxv) and `br`
to the entry point. Does not return — the loaded program is now
in control.

AT_PHDR / AT_PHENT / AT_PHNUM / AT_ENTRY are required by the
process-startup auxv vector per gabi 08 § Process Initialization.
-/

import LeanLoad.Discover
import LeanLoad.Plan.Layout
import LeanLoad.Plan.Reloc
import LeanLoad.FFI.Region
import LeanLoad.FFI.Exec

namespace LeanLoad.Load

open LeanLoad.FFI

/-- Stack size for the loaded program. Matches musl's default. -/
def stackBytes : USize := 8 * 1024 * 1024

/-- AArch64 program-header entry size (gabi 07: `Elf64_Phdr` is 56 B). -/
def phdrEntrySize : UInt64 := 56

/-- Allocate kernel-style stack and jump to entry. **Does not return.** -/
def transferControl (mainObj : Discover.LoadedObject) (plan : Plan.Layout.LoaderPlan)
    (bases : Plan.Reloc.Bases) (path : String) : IO Unit := do
  let some mainLayout := plan.layouts[0]?
    | throw (IO.userError "load: empty plan")
  let some mainBase := bases[0]?
    | throw (IO.userError "load: missing main base")
  let stack ← Region.mmapStack stackBytes
  let entry  := mainBase + mainLayout.entry.getD 0
  let phdrVa := mainBase + mainObj.elf.header.e_phoff
  let phnum  := mainObj.elf.header.e_phnum.toUInt64
  Exec.run entry phdrVa phdrEntrySize phnum 0 stack path

end LeanLoad.Load

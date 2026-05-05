/-
The "control transfer" half of `Load`: invoke each loaded object's
constructors, then build the kernel-style stack and jump.

Spec: gabi 08 § Initialization and Termination Functions, gabi 08 §
Process Initialization. ET_DYN init-array entries are relative
addresses (gabi 07 § Base Address) and need the chosen base added;
ET_EXEC entries are already absolute. AT_PHDR / AT_PHENT / AT_PHNUM /
AT_ENTRY in the auxv are required by the process-startup contract.

The `@[extern]` declarations at the top are the trust-boundary half:
two C calls into `runtime/exec.c`. The orchestration below drives them.
-/

import LeanLoad.Discover
import LeanLoad.Plan.Layout
import LeanLoad.Plan.Reloc
import LeanLoad.Region

namespace LeanLoad.Load

open LeanLoad

-- ============================================================================
-- Externs (`runtime/exec.c`)
-- ============================================================================

/-- Hand control to a loaded image.

    Builds the kernel-style exec stack on `stack` (argc, argv[],
    envp[], auxv[]), switches SP to it, and jumps to `entry`.
    **Does not return** — the loaded program owns the process.

    Auxv entries supplied:
    - `AT_PHDR` / `AT_PHENT` / `AT_PHNUM` if `phdrVa ≠ 0` (real
      glibc/musl need these for `dl_iterate_phdr` and stack-protector
      setup).
    - `AT_PAGESZ = 4096`.
    - `AT_BASE` if `baseVa ≠ 0` (the dynamic linker base, normally 0
      since we are the loader).
    - `AT_ENTRY = entry`.
    - `AT_RANDOM` pointing at 16 bytes on the stack (deterministic for
      now; satisfies stack canary readers).

    AArch64 only at present. -/
@[extern "leanload_exec_run"]
opaque execAndJump
  (entry  : UInt64)
  (phdrVa : UInt64)
  (phent  : UInt64)
  (phnum  : UInt64)
  (baseVa : UInt64)
  (stack  : @& LeanLoad.Region.Region)
  (argv0  : @& String) : IO Unit

/-- Call a constructor / destructor function by its absolute address.
    Signature per gabi 08: `void (*)(int argc, char **argv, char **envp)`.
    We pass `(0, NULL, NULL)`; freestanding ctors typically ignore them. -/
@[extern "leanload_exec_call_ctor"]
opaque callCtor (addr : UInt64) : IO Unit

-- ============================================================================
-- Init / fini invocation
-- ============================================================================

/-- Call every entry of one object's `DT_INIT_ARRAY`. -/
def runObjectInits (lm : Discover.LinkMap) (bases : Plan.Reloc.Bases)
    (objectIdx : Nat) : IO Unit := do
  let some obj := lm.objects[objectIdx]? | return ()
  let some base := bases[objectIdx]? | return ()
  let isExec := obj.elf.header.e_type = 2
  for entry in obj.elf.initArr do
    let fnAddr := if isExec then entry else base + entry
    if fnAddr != 0 then callCtor fnAddr

/-- Call constructors for every object in `initOrder`, including main. -/
def runInits (lm : Discover.LinkMap) (bases : Plan.Reloc.Bases)
    (plan : Plan.Layout.LoaderPlan) : IO Unit := do
  for objectIdx in plan.initOrder do
    runObjectInits lm bases objectIdx

-- ============================================================================
-- Stack + jump (does not return)
-- ============================================================================

/-- Stack size for the loaded program. Matches musl's default (8 MiB). -/
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
  execAndJump entry phdrVa phdrEntrySize phnum 0 stack path

end LeanLoad.Load

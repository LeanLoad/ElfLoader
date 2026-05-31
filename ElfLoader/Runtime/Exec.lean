/-
Final execution runtime operations.

Constructors and the final jump are intentionally separated from memory loading:
they run user code / transfer control and are not part of the pure finalized
load-op tree.
-/

import ElfLoader.Runtime

namespace ElfLoader

namespace Runtime

@[extern "elfloader_exec_call_ctor"]
private opaque callCtorRaw (addr : UInt64) : IO Unit

@[extern "elfloader_exec_run"]
private opaque execAndJumpRaw
  (entry  : UInt64)
  (programHeaderVa : UInt64)
  (phent  : UInt64)
  (phnum  : UInt64)
  (baseVa : UInt64)
  (stackVa : UInt64)
  (stackLen : UInt64)
  (argv0  : @& String) : IO Unit

/-- Call one constructor function in the loaded image. -/
def callCtor (addr : UInt64) : IO Unit :=
  callCtorRaw addr

/-- Transfer control to the loaded program. Does not return on success. -/
def execAndJump (a : ExecArgs) : IO Unit :=
  execAndJumpRaw a.entry a.programHeaderVa a.phent a.phnum a.baseVa
    a.stackVa a.stackLen a.argv0

end Runtime

end ElfLoader

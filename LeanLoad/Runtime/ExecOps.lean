/-
Final execution runtime capability.

Constructors and the final jump are intentionally separated from memory loading:
they run user code / transfer control and are not part of the pure finalized
load-op tree.
-/

namespace LeanLoad

namespace Runtime

/-- Arguments for the final non-returning transfer to the loaded program. -/
structure ExecArgs where
  entry           : UInt64
  programHeaderVa : UInt64
  phent           : UInt64
  phnum           : UInt64
  baseVa          : UInt64
  stackVa         : UInt64
  stackLen        : UInt64
  argv0           : String
  deriving Repr, Inhabited

/-- Operations that execute loaded code. -/
structure ExecOps (m : Type → Type) where
  callCtor    : UInt64 → m Unit
  execAndJump : ExecArgs → m Unit

namespace ExecOps

@[extern "leanload_exec_call_ctor"]
private opaque callCtorRaw (addr : UInt64) : IO Unit

@[extern "leanload_exec_run"]
private opaque execAndJumpRaw
  (entry  : UInt64)
  (programHeaderVa : UInt64)
  (phent  : UInt64)
  (phnum  : UInt64)
  (baseVa : UInt64)
  (stackVa : UInt64)
  (stackLen : UInt64)
  (argv0  : @& String) : IO Unit

/-- Production execution ops backed by the C runtime. -/
def io : ExecOps IO :=
  { callCtor := callCtorRaw
    execAndJump := fun a =>
      execAndJumpRaw a.entry a.programHeaderVa a.phent a.phnum a.baseVa
        a.stackVa a.stackLen a.argv0 }

end ExecOps

end Runtime

end LeanLoad


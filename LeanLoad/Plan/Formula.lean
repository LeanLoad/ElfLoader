/-
Per-`e_machine` relocation-formula dispatch.

The pure planner (`Plan.Reloc`) is parametric over a `Formula`; this
file picks the right one for a given binary's `e_machine`. Lives in a
separate module so both `Main` and the test driver can import it
without pulling each other in.
-/

import LeanLoad.Spec.Header
import LeanLoad.Spec.Reloc.Aarch64
import LeanLoad.Spec.Reloc.X86_64
import LeanLoad.Plan.Reloc

namespace LeanLoad.Plan

/-- Pick the relocation formula for `machine` (an `e_machine` value).
    `none` for any unsupported machine. -/
def formulaFor (machine : UInt16) : Option Plan.Reloc.Formula :=
  if machine = Spec.Header.EM_AARCH64 then some Spec.Reloc.Aarch64.formula
  else if machine = Spec.Header.EM_X86_64 then some Spec.Reloc.X86_64.formula
  else none

end LeanLoad.Plan

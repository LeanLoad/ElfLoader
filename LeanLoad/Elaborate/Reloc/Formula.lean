/-
Per-`e_machine` relocation-formula dispatch.

Spec basis: gabi 02 § ELF Identification (`e_machine` selects the
per-arch psABI), gabi 06 § Relocation, and the per-arch supplements
(AArch64 ELF ABI, x86-64 psABI § Relocation Types).
-/

import LeanLoad.Elaborate.Reloc.Aarch64
import LeanLoad.Elaborate.Reloc.X86_64

namespace LeanLoad.Elaborate

-- e_machine values (subset; full registry in gabi appendix `a-emachine.rst`)
def EM_X86_64  : UInt16 := 62
def EM_AARCH64 : UInt16 := 183

/-- Pick the relocation formula for `machine` (an `e_machine` value).
    `none` for any unsupported machine. -/
def formulaFor (machine : UInt16) : Option Formula :=
  if machine = EM_AARCH64 then some Aarch64.formula
  else if machine = EM_X86_64 then some X86_64.formula
  else none

end LeanLoad.Elaborate

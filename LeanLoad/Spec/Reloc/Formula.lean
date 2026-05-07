/-
Per-`e_machine` relocation-formula dispatch.

Spec basis: gabi 02 § ELF Identification (`e_machine` selects the
per-arch psABI), gabi 06 § Relocation (the `S, A, B, P` formula
notation lives in `Spec.Reloc`), and the per-arch supplements
(AArch64 ELF ABI, x86-64 psABI § Relocation Types) that supply the
per-type tables in `Spec/Reloc/{Aarch64,X86_64}.lean`.
-/

import LeanLoad.Spec.Header
import LeanLoad.Spec.Reloc.Aarch64
import LeanLoad.Spec.Reloc.X86_64

namespace LeanLoad.Spec.Reloc

open LeanLoad

/-- Pick the relocation formula for `machine` (an `e_machine` value).
    `none` for any unsupported machine. -/
def formulaFor (machine : UInt16) : Option Formula :=
  if machine = Header.EM_AARCH64 then some Aarch64.formula
  else if machine = Header.EM_X86_64 then some X86_64.formula
  else none

end LeanLoad.Spec.Reloc

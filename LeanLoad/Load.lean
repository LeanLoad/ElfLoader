/-
`LeanLoad.Load` — IO orchestration.

Trusted module that ties the verified core (`Parse`, `Plan`) to the
FFI layer (`runtime/`). Verified code (`Parse/`, `Plan/`) must not
import `LeanLoad.FFI`; everything that crosses into the kernel goes
through here.

Pipeline (each substage is its own file under `Load/`):
  Discover → Resolve → Plan → Materialize → Reloc → Apply → Init → Exec
-/

import LeanLoad.Parse
import LeanLoad.Plan
import LeanLoad.Discover
import LeanLoad.Load.Materialize
import LeanLoad.Load.Apply
import LeanLoad.Load.Init
import LeanLoad.Load.Exec

namespace LeanLoad.Load

open LeanLoad

/-- Lower-case hex string of a `Nat`, no `0x` prefix. -/
private def Nat.hex (n : Nat) : String :=
  String.ofList (Nat.toDigits 16 n)

#guard Nat.hex 0 = "0"
#guard Nat.hex 0x4000b0 = "4000b0"
#guard Nat.hex 0xdeadbeef = "deadbeef"

/-- Plan a link map: layouts + init/fini orders. Pure. -/
def planFor (lm : Discover.LinkMap) : Plan.Layout.LoaderPlan :=
  Plan.Layout.fromLinkMap lm
    (Plan.Init.initOrder lm)
    (Plan.Init.finiOrder lm)

/-- Pick the architecture-specific relocation formula based on `e_machine`.
    Currently only EM_AARCH64 (183) is implemented; binaries for
    other machines silently get the AArch64 formula and will fail to
    relocate. TODO: add EM_X86_64 (62) and reject unknown values. -/
def formulaFor (_machine : UInt32) : Plan.Reloc.Formula :=
  Plan.Reloc.Aarch64.formula

/-- Discover + plan + materialise + relocate + run inits + jump.
    **Does not return.** Pipeline structure:

    1. Discover (IO):     path → link map
    2. Resolve (pure):    link map → resolution table
    3. Plan (pure):       link map → layouts + init order  (no bases)
    4. Materialise (IO):  layouts → regions × kernel-chosen bases
    5. Reloc (pure):      link map × resolution × bases → writes
    6. Apply (IO):        writes → memory mutated
    7. Init (IO):         bases × init order → constructors called
    8. Exec (IO):         no return -/
def load (path : String) : IO Unit := do
  let lm ← Discover.discover path
  let some mainObj := lm.objects[0]?
    | throw (IO.userError "load: empty link map")
  let rt   := Plan.Resolve.buildTable lm
  let plan := planFor lm
  let (allRegions, bases) ← materializeAll lm plan
  let formula := formulaFor mainObj.elf.header.e_machine.toUInt32
  let writes := Plan.Reloc.plan formula lm bases rt
  applyAllRelocs allRegions bases writes
  runInits lm bases plan
  transferControl mainObj plan bases path

/-- `--inspect`: print the plan, do not run. -/
def inspect (path : String) : IO Unit := do
  let lm ← Discover.discover path
  let plan := planFor lm
  IO.println s!"objects: {plan.layouts.size}"
  for lyt in plan.layouts do
    let some obj := lm.objects[lyt.objectIdx]? | continue
    IO.println s!"  [{lyt.objectIdx}] {obj.name} ({lyt.mappings.size} mappings)"
    if let some e := lyt.entry then
      IO.println s!"    entry: 0x{Nat.hex e.toNat}"
    for m in lyt.mappings do
      IO.println s!"    vaddr=0x{Nat.hex m.vaddr.toNat} len=0x{Nat.hex m.length.toNat} prot={m.prot}"
  IO.println s!"init order: {plan.initOrder}"
  IO.println s!"fini order: {plan.finiOrder}"

end LeanLoad.Load

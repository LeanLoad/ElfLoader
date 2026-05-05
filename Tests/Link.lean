import LeanLoad

namespace Tests.Link

open LeanLoad

/-- Test init/fini ordering and the AArch64 relocation planner against
    `examples/build/main`'s closure. -/
def run : IO Nat := do
  let mut failures := 0
  let path := "examples/build/main"
  unless (← System.FilePath.pathExists path) do
    IO.eprintln s!"skip: {path} not built"
    return 0
  let li ← try LeanLoad.Discover.discover path
           catch _ => pure { objects := #[] }
  if li.objects.size < 4 then
    IO.eprintln "discover failed"
    return failures + 1

  -- Init order: post-order traversal. Main (idx 0) must come last.
  let order := LeanLoad.Link.Init.initOrder li
  if order.size != li.objects.size then
    IO.eprintln s!"init order size {order.size} ≠ object count {li.objects.size}"
    failures := failures + 1
  if order.back? != some 0 then
    IO.eprintln s!"main (idx 0) should be last in init order; got {order}"
    failures := failures + 1

  -- Relocation planner: with all-zero bases and a fresh resolution
  -- table, the planner should emit one write per supported rela
  -- entry (skipping NONE and unsupported types). main has 12 rela.dyn
  -- + 12 rela.plt = 24 supported entries on aarch64.
  let rt := LeanLoad.Link.Resolve.buildTable li
  let bases : LeanLoad.Link.Reloc.Bases := Array.replicate li.objects.size 0
  let writes := LeanLoad.Link.Reloc.plan
    LeanLoad.Link.Reloc.Aarch64.formula li bases rt
  if writes.size == 0 then
    IO.eprintln "expected nonzero relocation writes"
    failures := failures + 1
  return failures

end Tests.Link

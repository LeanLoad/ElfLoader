import LeanLoad

namespace Tests.Resolve

/-- Discover `examples/build/main`'s closure, build the resolution
    table, check that:
    - cross-library `libfoo_print` (from libfoo.so) resolves, into
      libfoo.so;
    - cross-library `libbar_step` resolves, into libbar.so;
    - the cycle libbar↔libbaz is resolved both ways;
    - the unresolved set is empty (modulo unnamed `STN_UNDEF`). -/
def run : IO Nat := do
  let mut failures := 0
  let path := "examples/build/main"
  unless (← System.FilePath.pathExists path) do
    IO.eprintln s!"skip: {path} not built"
    return 0
  let li ← try LeanLoad.Discover.discover path
           catch e =>
             IO.eprintln s!"discover failed: {e}"
             pure { objects := #[] }
  if li.objects.size < 4 then
    IO.eprintln s!"expected ≥ 4 objects, got {li.objects.size}"
    return failures + 1

  let table := LeanLoad.Link.Resolve.buildTable li

  -- Every named undefined reference in our test fixtures should resolve.
  -- libfoo/libbar/libbaz expose only public symbols our binary uses,
  -- and libc supplies the rest.
  if table.missing.size != 0 then
    IO.eprintln s!"expected 0 missing, got {table.missing.size}:"
    for u in table.missing[:5] do
      IO.eprintln s!"  unresolved: '{u.name}' from object[{u.objectIdx}]"
    failures := failures + 1

  -- Spot checks: specific symbols resolve into their expected providers.
  let expectations : List (String × String) := [
    ("libfoo_print", "libfoo.so"),
    ("libbar_step",  "libbar.so"),
    ("libbaz_step",  "libbaz.so")
  ]
  for (sym, expectedProvider) in expectations do
    match LeanLoad.Link.Resolve.resolveByName li sym with
    | none =>
      IO.eprintln s!"{sym} did not resolve"
      failures := failures + 1
    | some r =>
      match li.objects[r.objectIdx]? with
      | none => failures := failures + 1
      | some obj =>
        if obj.name != expectedProvider then
          IO.eprintln s!"{sym} resolved to {obj.name}, expected {expectedProvider}"
          failures := failures + 1

  return failures

end Tests.Resolve

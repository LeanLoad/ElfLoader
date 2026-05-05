import LeanLoad

namespace Tests.Discover

/-- The full closure of `examples/build/main` should be exactly five
    objects: main, libfoo.so, libbar.so, libbaz.so, libc.so.
    libbar↔libbaz form a cycle (mutual NEEDED); the SONAME-keyed
    dedup must terminate the BFS. -/
def expectedNames : Array String :=
  #["main", "libfoo.so", "libbar.so", "libbaz.so", "libc.so"]

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
  let names := li.objects.map (·.name)

  -- Object count: exactly the expected closure.
  if li.objects.size != expectedNames.size then
    IO.eprintln s!"expected {expectedNames.size} objects, got {li.objects.size}: {names}"
    failures := failures + 1

  -- Each expected name should appear (the first one — main — has its
  -- canonical name = path since we don't set DT_SONAME on executables).
  for expected in expectedNames[1:] do
    if !names.any (· == expected) then
      IO.eprintln s!"{expected} missing from closure: {names}"
      failures := failures + 1

  -- The cycle libbar↔libbaz should not produce duplicate entries.
  for nm in names do
    let occurrences := names.filter (· == nm) |>.size
    if occurrences > 1 then
      IO.eprintln s!"{nm} appears {occurrences} times — dedup failed"
      failures := failures + 1

  return failures

end Tests.Discover

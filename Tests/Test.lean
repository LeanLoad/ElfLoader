import Tests.Parse

/-- Top-level test runner. Each module exposes `run : IO Nat` returning
    its failure count. Aggregate, print, exit non-zero on any failure. -/
def main : IO UInt32 := do
  let suites : List (String × IO Nat) := [
    ("Parse", Tests.Parse.run)
  ]
  let mut failures : Nat := 0
  for (name, suite) in suites do
    let f ← suite
    if f = 0 then
      IO.println s!"  ok    {name}"
    else
      IO.println s!"  FAIL  {name} ({f})"
      failures := failures + f
  if failures = 0 then
    IO.println "all tests passed"
    return 0
  else
    IO.eprintln s!"{failures} test(s) failed"
    return 1

import LeanLoad

namespace Tests.Parse

-- # Parse tests
--
-- Template — wire real assertions in here as `Parse/` modules come
-- online. Three patterns are demonstrated below:
--
-- 1. `#guard` for compile-time invariants on inline data.
-- 2. Loading a real binary from `examples/build/` via `loadExample`.
-- 3. Golden-file comparison via `goldenCheck`.
--
-- `#eval` works in this file: from the project root,
-- `#eval IO.FS.readBinFile "examples/build/main"` returns the bytes
-- of the example binary.

/-- ELF magic: every loadable ELF starts with these four bytes. -/
def elfMagic : ByteArray :=
  ByteArray.mk #[0x7f, 0x45, 0x4c, 0x46]

#guard elfMagic.size = 4
#guard elfMagic[0]! = 0x7f

/-- Load an example binary by name. Path is relative to the project
    root, where `lake test` and editor `#eval` run from. -/
def loadExample (name : String) : IO ByteArray :=
  IO.FS.readBinFile s!"examples/build/{name}"

/-- Compare a string against a checked-in golden file. Updates the
    golden when `LEANLOAD_BLESS=1` is set in the environment. -/
def goldenCheck (path actual : String) : IO Bool := do
  if (← IO.getEnv "LEANLOAD_BLESS") == some "1" then
    IO.FS.writeFile path actual
    return true
  let expected ← (try IO.FS.readFile path catch _ => pure "")
  if expected == actual then
    return true
  IO.eprintln s!"golden mismatch in {path} (run with LEANLOAD_BLESS=1 to update)"
  return false

/-- Run all Parse tests; returns the number of failures. -/
def run : IO Nat := do
  let mut failures := 0

  -- Sample test: ELF magic constant is what we expect at runtime too.
  if elfMagic.size != 4 || elfMagic[0]! != 0x7f then
    IO.eprintln "elfMagic invariant failed"
    failures := failures + 1

  -- Template for a golden test — uncomment once `LeanLoad.Parse` exists:
  --   let bytes ← loadExample "main"
  --   match LeanLoad.Parse.parseHeader bytes with
  --   | .ok h =>
  --       let actual := toString (repr h)
  --       if !(← goldenCheck "Tests/golden/main.header.txt" actual) then
  --         failures := failures + 1
  --   | .error e => IO.eprintln s!"parse failed: {e}"; failures := failures + 1

  return failures

end Tests.Parse

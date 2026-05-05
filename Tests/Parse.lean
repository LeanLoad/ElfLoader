import LeanLoad

namespace Tests.Parse

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

/-- End-to-end smoke test: parse `examples/build/main` and assert basics. -/
def smokeTest : IO Nat := do
  let mut failures := 0
  let bytes ← (try loadExample "main"
               catch _ => IO.eprintln "skip: examples/build/main not built"; pure ⟨#[]⟩)
  if bytes.size = 0 then return 0  -- skipped

  match LeanLoad.Parse.Parser.run bytes LeanLoad.Parse.Header.parse with
  | .error e =>
      IO.eprintln s!"Header.parse failed: {e}"
      failures := failures + 1
  | .ok h =>
      -- Should be a PIE (shared-object form), not a relocatable.
      if h.e_type != LeanLoad.Parse.Header.ET_DYN then
        IO.eprintln s!"e_type: expected ET_DYN={LeanLoad.Parse.Header.ET_DYN}, got {h.e_type}"
        failures := failures + 1
      -- ehsize on ELF64 is 64 bytes.
      if h.e_ehsize != 64 then
        IO.eprintln s!"e_ehsize: expected 64, got {h.e_ehsize}"
        failures := failures + 1
      -- phentsize on ELF64 must be 56.
      if h.e_phentsize != 56 then
        IO.eprintln s!"e_phentsize: expected 56, got {h.e_phentsize}"
        failures := failures + 1
      -- Program header table should parse without error.
      match LeanLoad.Parse.Parser.run bytes
              (LeanLoad.Parse.Program.parseTable h.e_phoff.toNat h.e_phnum.toNat) with
      | .error e =>
          IO.eprintln s!"Program.parseTable failed: {e}"
          failures := failures + 1
      | .ok phs =>
          if phs.size != h.e_phnum.toNat then
            IO.eprintln s!"phnum mismatch: header says {h.e_phnum}, parsed {phs.size}"
            failures := failures + 1

  -- Full aggregate parse — header + dyn + strtab + needed + runpath + rela.
  match LeanLoad.Parse.File.parse bytes with
  | .error e =>
      IO.eprintln s!"File.parse failed: {e}"
      failures := failures + 1
  | .ok elf =>
      -- main depends on libfoo + libbar, so DT_NEEDED should have ≥ 2 entries
      -- (musl also adds a libc NEEDED).
      if elf.needed.size < 3 then
        IO.eprintln s!"expected ≥ 3 NEEDED entries, got {elf.needed.size}: {elf.needed}"
        failures := failures + 1
      -- libfoo and libbar should be among them.
      if !elf.needed.any (· == "libfoo.so") then
        IO.eprintln s!"libfoo.so not in NEEDED: {elf.needed}"
        failures := failures + 1
      if !elf.needed.any (· == "libbar.so") then
        IO.eprintln s!"libbar.so not in NEEDED: {elf.needed}"
        failures := failures + 1
      -- RUNPATH should be the rpath we baked in.
      if elf.runpath.isNone then
        IO.eprintln "expected DT_RUNPATH set"
        failures := failures + 1
  return failures

/-- Run all Parse tests; returns the number of failures. -/
def run : IO Nat := do
  let mut failures := 0
  if elfMagic.size != 4 || elfMagic[0]! != 0x7f then
    IO.eprintln "elfMagic invariant failed"
    failures := failures + 1
  failures := failures + (← smokeTest)
  return failures

end Tests.Parse

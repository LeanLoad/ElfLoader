import LeanLoad

/-- LeanLoad CLI.

    `leanload <elf>`            — load and run a binary via kernel-style
                                  exec. Static or dynamic; single
                                  pipeline (Discover → Link → Load).
                                  Does not return.
    `leanload --inspect <elf>`  — print the planned layout, do not run.
-/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--inspect", path] =>
    LeanLoad.Load.inspect path
    return 0
  | [path] =>
    LeanLoad.Load.load path
    return 0  -- unreachable; loaded program terminates the process
  | _ =>
    IO.eprintln "usage: leanload [--inspect] <path-to-elf>"
    return 1

/-
`LeanLoad.Parse` — pure ELF parsing.

Each sub-module corresponds to one gabi chapter; `Bytes` provides the
parser monad and primitives that the others build on.
-/

import LeanLoad.Parse.Bytes
import LeanLoad.Parse.Header
import LeanLoad.Parse.Program
import LeanLoad.Parse.Dynamic
import LeanLoad.Parse.Symbol
import LeanLoad.Parse.Reloc
import LeanLoad.Parse.File

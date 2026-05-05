/-
Byte-level reader for string tables.
Spec types live in `LeanLoad.Spec.StringTable`.
-/

import LeanLoad.Parse.Bytes
import LeanLoad.Spec.StringTable

namespace LeanLoad.Parse.StringTable

open LeanLoad.Parse.Bytes
open LeanLoad.Spec.StringTable

/-- Read a string table out of the file: `offset .. offset+size`. -/
def parse (offset size : Nat) : Parser StringTable := do
  seek offset
  slice size

end LeanLoad.Parse.StringTable

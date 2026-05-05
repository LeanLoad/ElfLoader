/-
`LeanLoad.FFI` — extern declarations for the C runtime under `runtime/`.

This is the trust boundary: anything reachable through these modules
is unverified, audited code. Only `LeanLoad.Load` should import this
namespace; verified code (`Parse/`, `Link/`) must not.
-/

import LeanLoad.FFI.Region
import LeanLoad.FFI.Exec

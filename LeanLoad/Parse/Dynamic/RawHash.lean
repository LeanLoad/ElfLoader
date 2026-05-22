/-
gabi 08 § Hash Table — header of `DT_HASH`-pointed section.

The hash section starts with two `UInt32` fields — `nbucket` and
`nchain` — followed by the bucket and chain arrays. LeanLoad only
needs `nchain`: it's the count of `.dynsym` entries (gabi 08 fixes
`nchain == dynsym.entries`), the only section whose size doesn't
pair with a `DT_*SZ` tag.

`--hash-style=both` in the build ensures `DT_HASH` is present
alongside `DT_GNU_HASH` (the modern default); a GNU-only binary
would force chain walking.
-/

import LeanLoad.Parse.Decode
import LeanLoad.Parse.Deriving

namespace LeanLoad.Parse

/-- 8-byte header of the `DT_HASH` section. Bucket and chain arrays
    follow at file-offset + 8 but LeanLoad never reads them — only
    `nchain` matters as the dynsym entry count. -/
structure RawHash where
  nbucket : UInt32
  nchain  : UInt32
  deriving Repr, Inhabited, BytesDecode

/-- Size of the header read: 4 + 4 = 8 bytes. Bucket / chain arrays
    that follow are not parsed. -/
def RawHashSize : Nat := 8


end LeanLoad.Parse

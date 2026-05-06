/-
Byte-level reader for `DT_GNU_HASH`. Consumes the table layout
(gnu-gabi § Hashes) and defers the actual count derivation to
`Spec.GnuHash.symCount` (see that module for the linker invariant
we rely on, since gnu-gabi defines no count tag and the algorithm
itself is community lore).
-/

import LeanLoad.Parse.Bytes
import LeanLoad.Spec.GnuHash

namespace LeanLoad.Parse.GnuHash

open LeanLoad.Parse.Bytes

/-- Read a GNU hash table at file offset `off` and return the dynsym
    count via `Spec.GnuHash.symCount`. Reads buckets exactly, then
    reads chain entries up to the end of the byte buffer (the chain's
    real length is unbounded by the table itself; the caller's file
    size is the only natural upper bound). -/
def parseSymCount (off : Nat) : Parser Nat := do
  seek off
  let nbuckets   := (← u32le).toNat
  let symoffset  := (← u32le).toNat
  let bloomWords := (← u32le).toNat
  let _bloomShift ← u32le
  skip (bloomWords * 8)  -- ELF64: each bloom word is 64 bits
  let mut buckets : Array UInt32 := Array.mkEmpty nbuckets
  for _ in [:nbuckets] do
    buckets := buckets.push (← u32le)
  let s ← get
  let chainBound := (s.bytes.size - s.pos) / 4
  let mut chain : Array UInt32 := Array.mkEmpty chainBound
  for _ in [:chainBound] do
    chain := chain.push (← u32le)
  match Spec.GnuHash.symCount symoffset buckets chain with
  | some n => return n
  | none   => throw "parseSymCount: chain has no end marker (malformed)"

end LeanLoad.Parse.GnuHash

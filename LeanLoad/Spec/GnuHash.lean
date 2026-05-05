/-
GNU hash table — `DT_GNU_HASH`.

Spec: gnu-gabi (`third_party/gnu-gabi/program-loading-and-dynamic-linking.txt`)
§ Hashes. A faster, GNU-only alternative to gabi 08 § Hash Table;
emitted by default on modern x86-64 Linux toolchains.

Layout (ELF64). Four-`u32` header followed by three arrays:

    (nbuckets, symoffset, bloom_words, bloom_shift)
    bloom   : UInt64[bloom_words]    -- bloom filter (skipped here)
    buckets : UInt32[nbuckets]       -- dynsym index of first hashed
                                        symbol per bucket (0 = empty)
    chain   : UInt32[…]              -- pseudo-hash per hashed symbol;
                                        last entry of each bucket has
                                        bit 0 set

The dynsym count is *not* given by any tag. We derive it from the
chain by exploiting the linker invariant that the highest hashed
dynsym index equals `max(buckets) + (steps to next end marker)`.
-/

namespace LeanLoad.Spec.GnuHash

/-- Maximum bucket value: the highest dynsym index referenced by any
    non-empty bucket. `0` when every bucket is empty (no hashed
    symbols). -/
def maxBucket (buckets : Array UInt32) : Nat :=
  buckets.foldl (init := 0) (fun m b => max m b.toNat)

/-- `Some` of the smallest `j ≥ start` with `chain[j].land 1 = 1`,
    i.e. the next end-of-bucket marker; `none` if no such index
    exists. Implemented via `List.findIdx?` on the dropped tail. -/
def findEndMarker (chain : Array UInt32) (start : Nat) : Option Nat :=
  ((chain.toList.drop start).findIdx? (fun w => w &&& 1 == 1)).map (· + start)

/-- Derive the dynsym count from a parsed GNU hash table.

    Assumes the gnu-gabi/binutils linker invariant (not stated in
    gnu-gabi itself; see `bfd_elf_size_dynsym_hash_dynstr`):

    1. Hashed symbols occupy a contiguous tail of `.dynsym` starting
       at index `symoffset`. So every non-zero `buckets[i] ≥ symoffset`.
    2. The chain has exactly one entry per hashed symbol; the last
       entry of each non-empty bucket has bit 0 set.

    Under these, `count = max(buckets) + steps-to-next-end-marker + 1`.
    Returns `none` if no end marker is found (malformed table) or if
    every bucket is empty *and* `symoffset = 0` (degenerate; treated
    as `some 0` since there really are zero hashed symbols then). -/
def symCount (symoffset : Nat) (buckets chain : Array UInt32) : Option Nat :=
  let lastFirst := maxBucket buckets
  if lastFirst = 0 then
    some symoffset
  else
    let startIdx := lastFirst - symoffset
    (findEndMarker chain startIdx).map (fun j => lastFirst + (j - startIdx) + 1)

-- Sanity. A 1-bucket table with `symoffset = 1`, `buckets[0] = 1`
-- (one hashed symbol at index 1), `chain[0]` end-marked: count = 2.
#guard symCount 1 #[1] #[0x1] = some 2
-- Two symbols at indices 1, 2 in one bucket: chain[1] is the marker.
#guard symCount 1 #[1] #[0x0, 0x1] = some 3
-- Empty buckets ⇒ symoffset.
#guard symCount 5 #[0, 0, 0] #[] = some 5
-- Malformed: bucket says there's a symbol but chain has no end marker.
#guard symCount 1 #[1] #[0x0, 0x0] = none

end LeanLoad.Spec.GnuHash

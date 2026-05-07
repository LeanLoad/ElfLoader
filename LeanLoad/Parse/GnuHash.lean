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

import LeanLoad.Parse.Bytes

namespace LeanLoad.Parse.GnuHash

open LeanLoad.Parse.Bytes

-- ============================================================================
-- Pure derivation: `symCount` from buckets + chain.
-- ============================================================================

/-- Maximum bucket value: the highest dynsym index referenced by any
    non-empty bucket. `0` when every bucket is empty (no hashed
    symbols). -/
def maxBucket (buckets : Array UInt32) : Nat :=
  buckets.foldl (init := 0) (fun m b => max m b.toNat)

/-- `Some` of the smallest `j ≥ start` with `chain[j].land 1 = 1`,
    i.e. the next end-of-bucket marker; `none` if no such index
    exists. -/
def findEndMarker (chain : Array UInt32) (start : Nat) : Option Nat :=
  ((chain.toList.drop start).findIdx? (fun w => w &&& 1 == 1)).map (· + start)

section Example
#guard findEndMarker #[0x10, 0x20, 0x31, 0x40] 0 = some 2
#guard findEndMarker #[0x10, 0x20, 0x31, 0x40] 3 = none
#guard findEndMarker #[0x10, 0x20] 5 = none
#guard findEndMarker #[0x1, 0x3, 0x5] 0 = some 0
#guard findEndMarker #[0x1, 0x3, 0x5] 1 = some 1
end Example

/-- Derive the dynsym count from a parsed GNU hash table.

    gnu-gabi documents the *layout* (4-u32 header, bloom filter,
    buckets, chain with end-of-bucket bit-0 marker) but **does not**
    specify a count-derivation algorithm. The recipe below — folklore
    among real loaders (glibc / musl / lld / binutils all implement
    it; see `bfd_elf_size_dynsym_hash_dynstr` for one reference) —
    relies on two invariants the GNU linker maintains:

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

#guard symCount 1 #[1] #[0x1] = some 2
#guard symCount 1 #[1] #[0x0, 0x1] = some 3
#guard symCount 5 #[0, 0, 0] #[] = some 5
#guard symCount 1 #[1] #[0x0, 0x0] = none

-- ============================================================================
-- Byte-level reader
-- ============================================================================

/-- Read a GNU hash table at file offset `off` and return the dynsym
    count via `symCount`. Reads buckets exactly, then reads chain
    entries up to the end of the byte buffer (the chain's real length
    is unbounded by the table itself; the caller's file size is the
    only natural upper bound). -/
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
  match symCount symoffset buckets chain with
  | some n => return n
  | none   => throw "parseSymCount: chain has no end marker (malformed)"

-- ============================================================================
-- Soundness theorems for `symCount`.
--
-- gnu-gabi defines no count tag, so the algorithm is folklore (see
-- `symCount`'s docstring). These theorems pin down the small properties
-- we *can* prove without modeling the linker invariant in full:
--   * empty buckets ⇒ count = symoffset (no hashed symbols)
--   * `findEndMarker` indices are bounded `[start, cs.size)`
--   * a non-empty result strictly exceeds the largest bucket value,
--     i.e. covers every dynsym index any bucket could reference
-- ============================================================================

/-- All-empty buckets ⇒ `symCount` returns `symoffset` exactly.
    Captures: when the hash table references no symbols, the dynsym
    has only the `symoffset` synthetic entries. -/
theorem symCount_empty_buckets (so : Nat) (cs : Array UInt32) :
    symCount so #[] cs = some so := by
  unfold symCount maxBucket
  simp

/-- `findEndMarker` returns indices ≥ its `start` argument. -/
theorem findEndMarker_ge (cs : Array UInt32) (start j : Nat) :
    findEndMarker cs start = some j → j ≥ start := by
  unfold findEndMarker
  intro h
  cases hk : (cs.toList.drop start).findIdx? (fun w => w &&& 1 == 1) with
  | none => rw [hk] at h; simp at h
  | some k => rw [hk] at h; simp at h; omega

/-- `findEndMarker` only returns valid in-bounds chain indices. -/
theorem findEndMarker_lt_size (cs : Array UInt32) (start j : Nat) :
    findEndMarker cs start = some j → j < cs.size := by
  unfold findEndMarker
  intro h
  cases hk : (cs.toList.drop start).findIdx? (fun w => w &&& 1 == 1) with
  | none => rw [hk] at h; simp at h
  | some k =>
    rw [hk] at h; simp at h
    have hbound : k < (cs.toList.drop start).length :=
      (List.findIdx?_eq_some_iff_findIdx_eq.mp hk).1
    rw [List.length_drop, Array.length_toList] at hbound
    omega

/-- If `symCount` returns a non-empty-bucket result, that result is
    strictly greater than every bucket value. Soundness direction:
    we never report a count smaller than what the buckets imply. -/
theorem symCount_gt_maxBucket
    (so : Nat) (bs cs : Array UInt32) (n : Nat)
    (hpos : maxBucket bs > 0) :
    symCount so bs cs = some n → n > maxBucket bs := by
  intro h
  unfold symCount at h
  have hne : ¬ (maxBucket bs = 0) := by omega
  simp [hne] at h
  cases hf : findEndMarker cs (maxBucket bs - so) with
  | none => rw [hf] at h; simp at h
  | some j =>
    rw [hf] at h
    simp at h
    have hjge : j ≥ maxBucket bs - so := findEndMarker_ge _ _ _ hf
    omega

end LeanLoad.Parse.GnuHash

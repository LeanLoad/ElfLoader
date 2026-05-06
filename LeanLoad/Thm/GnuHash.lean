/-
GNU hash symbol-count derivation.

`Spec.GnuHash.symCount` derives the dynsym count from a parsed GNU
hash table. gnu-gabi defines no count tag, so the algorithm is
inferred from the layout (see `Spec/GnuHash.lean` docstring). These
theorems pin down the small properties we *can* prove without
modeling the linker invariant in full:
  * empty buckets ⇒ count = symoffset (no hashed symbols)
  * `findEndMarker` indices are bounded `[start, cs.size)`
  * a non-empty result strictly exceeds the largest bucket value,
    i.e. covers every dynsym index any bucket could reference
-/

import LeanLoad.Spec.GnuHash

namespace LeanLoad.Thm

open LeanLoad.Spec.GnuHash

/-- All-empty buckets ⇒ `symCount` returns `symoffset` exactly.
    Captures: when the hash table references no symbols, the dynsym
    has only the `symoffset` synthetic entries. -/
theorem symCount_empty_buckets (so : Nat) (cs : Array UInt32) :
    symCount so #[] cs = some so := by
  unfold symCount maxBucket
  simp

/-- `findEndMarker` returns indices ≥ its `start` argument; this is
    the standard `findIdx?`-shifted-by-`start` property. -/
theorem findEndMarker_ge (cs : Array UInt32) (start j : Nat) :
    findEndMarker cs start = some j → j ≥ start := by
  unfold findEndMarker
  intro h
  cases hk : (cs.toList.drop start).findIdx? (fun w => w &&& 1 == 1) with
  | none => rw [hk] at h; simp at h
  | some k => rw [hk] at h; simp at h; omega

/-- `findEndMarker` only returns valid in-bounds chain indices. The
    upper-bound counterpart of `findEndMarker_ge`; together they pin
    down the marker index to `[start, cs.size)`. -/
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
    strictly greater than every bucket value (i.e. greater than every
    dynsym index any bucket can reference). This is the soundness
    direction: we never report a count smaller than what the buckets
    already imply. -/
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

end LeanLoad.Thm

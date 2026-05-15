/-
Characterisation lemmas for the per-op denotations defined in
`Spec/Apply.lean`. Two shapes per op:

  · `apply_outside` — addresses outside the op's range are
    preserved (`(o.apply mem) a = mem a`).
  · `apply_inside`  — addresses inside the op's range read the
    op's intended value (`(o.apply mem) a = …`).

These are the structural building blocks the three soundness
theorems (`Spec/Soundness.lean`) compose:

  · Bytes-preserved: chain of mmap + zero + stores + mprotect →
    take the mmap's `apply_inside`, then propagate through later
    ops via `apply_outside` using disjointness from `LoadSafe`.

  · BSS-zeroed: same but starting from the zero op's
    `apply_inside`, or from the `Memory.zero` initial state if
    the byte falls in the full-page anonymous BSS region.

  · Relocs-applied: stores' `apply_inside` plus disjointness
    from later stores / mprotect.

All four ops have decidable in-range predicates, so the lemmas
discharge via plain `if_pos` / `if_neg` reductions on the
denotation's `if-then-else`.
-/

import LeanLoad.Spec.Apply

namespace LeanLoad

open LeanLoad.Spec

-- ============================================================================
-- MmapOp
-- ============================================================================

namespace MmapOp

/-- A byte outside the mmap's range is preserved. -/
theorem apply_outside {fs : File} {m : MmapOp} {mem : Memory} {a : UInt64}
    (h : ¬ (m.addr.toNat ≤ a.toNat ∧ a.toNat < m.addr.toNat + m.len.toNat)) :
    (m.apply fs mem) a = mem a := by
  unfold apply
  simp [h]

/-- A byte inside the mmap's range reads the corresponding file byte. -/
theorem apply_inside {fs : File} {m : MmapOp} {mem : Memory} {a : UInt64}
    (h_lo : m.addr.toNat ≤ a.toNat)
    (h_hi : a.toNat < m.addr.toNat + m.len.toNat) :
    (m.apply fs mem) a = fs.byte m.handle (m.offset + (a - m.addr)) := by
  unfold apply
  simp [h_lo, h_hi]

end MmapOp

-- ============================================================================
-- ZeroOp
-- ============================================================================

namespace ZeroOp

/-- A byte outside the zero's range is preserved. -/
theorem apply_outside {z : ZeroOp} {mem : Memory} {a : UInt64}
    (h : ¬ (z.addr.toNat ≤ a.toNat ∧ a.toNat < z.addr.toNat + z.len.toNat)) :
    (z.apply mem) a = mem a := by
  unfold apply
  simp [h]

/-- A byte inside the zero's range reads `0`. -/
theorem apply_inside {z : ZeroOp} {mem : Memory} {a : UInt64}
    (h_lo : z.addr.toNat ≤ a.toNat)
    (h_hi : a.toNat < z.addr.toNat + z.len.toNat) :
    (z.apply mem) a = 0 := by
  unfold apply
  simp [h_lo, h_hi]

end ZeroOp

-- ============================================================================
-- StoreOp
-- ============================================================================

namespace StoreOp

/-- A byte outside the store's range is preserved. -/
theorem apply_outside {s : StoreOp} {mem : Memory} {a : UInt64}
    (h : ¬ (s.addr.toNat ≤ a.toNat ∧ a.toNat < s.addr.toNat + s.byteLen.toNat)) :
    (s.apply mem) a = mem a := by
  unfold apply
  simp [h]

/-- A byte inside the store's range reads the corresponding LE byte of
    `s.value`. -/
theorem apply_inside {s : StoreOp} {mem : Memory} {a : UInt64}
    (h_lo : s.addr.toNat ≤ a.toNat)
    (h_hi : a.toNat < s.addr.toNat + s.byteLen.toNat) :
    (s.apply mem) a =
      (s.value >>> UInt64.ofNat (8 * (a.toNat - s.addr.toNat))).toUInt8 := by
  unfold apply
  simp [h_lo, h_hi]

end StoreOp

-- ============================================================================
-- MprotectOp — byte-level no-op, so `apply` is identity.
-- ============================================================================

namespace MprotectOp

@[simp] theorem apply_eq (p : MprotectOp) (mem : Memory) :
    p.apply mem = mem := rfl

theorem apply_at (p : MprotectOp) (mem : Memory) (a : UInt64) :
    (p.apply mem) a = mem a := rfl

end MprotectOp

end LeanLoad

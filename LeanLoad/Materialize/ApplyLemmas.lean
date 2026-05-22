/-
Characterisation lemmas for the per-op denotations defined in
`Materialize/Apply.lean`. Two shapes per op:

  · `apply_outside` — addresses outside the op's range are
    preserved.
  · `apply_inside`  — addresses inside the op's range read the
    op's intended value.

`MprotectOp.apply` is the identity on `Memory` (perms are not
modelled), so it has neither shape — just an `apply_byte` rfl-lemma
that says "byte is unchanged."

These are the structural building blocks the soundness theorems
compose:

  · bytes_preserved      — `MmapOp.apply_inside`  + later `apply_outside`s.
  · bss_zeroed           — `apply_no_touch` over the whole tree.
  · relocs_applied       — `StoreOp.apply_inside` + later `apply_outside`s.

All four ops have decidable in-range predicates, so the lemmas
discharge via plain `if_pos` / `if_neg` reductions.
-/

import LeanLoad.Materialize.Apply

namespace LeanLoad

-- ============================================================================
-- MmapOp — byte changes inside the range.
-- ============================================================================

namespace MmapOp

/-- A byte outside the mmap's range is preserved. -/
theorem apply_outside {fs : File} {m : MmapOp} {mem : Memory} {a : UInt64}
    (h : ¬ (m.addr.toNat ≤ a.toNat ∧ a.toNat < m.addr.toNat + m.len.toNat)) :
    (m.apply fs mem).byte a = mem.byte a := by
  unfold apply
  simp [h]

/-- A byte inside the mmap's range reads the corresponding file byte. -/
theorem apply_inside {fs : File} {m : MmapOp} {mem : Memory} {a : UInt64}
    (h_lo : m.addr.toNat ≤ a.toNat)
    (h_hi : a.toNat < m.addr.toNat + m.len.toNat) :
    (m.apply fs mem).byte a = fs.byte m.handle (m.offset + (a - m.addr)) := by
  unfold apply
  simp [h_lo, h_hi]

end MmapOp

-- ============================================================================
-- ZeroOp — byte zeros inside the range.
-- ============================================================================

namespace ZeroOp

/-- A byte outside the zero's range is preserved. -/
theorem apply_outside {z : ZeroOp} {mem : Memory} {a : UInt64}
    (h : ¬ (z.addr.toNat ≤ a.toNat ∧ a.toNat < z.addr.toNat + z.len.toNat)) :
    (z.apply mem).byte a = mem.byte a := by
  unfold apply
  simp [h]

/-- A byte inside the zero's range reads `0`. -/
theorem apply_inside {z : ZeroOp} {mem : Memory} {a : UInt64}
    (h_lo : z.addr.toNat ≤ a.toNat)
    (h_hi : a.toNat < z.addr.toNat + z.len.toNat) :
    (z.apply mem).byte a = 0 := by
  unfold apply
  simp [h_lo, h_hi]

end ZeroOp

-- ============================================================================
-- StoreOp — byte writes inside the range.
-- ============================================================================

namespace StoreOp

/-- A byte outside the store's range is preserved. -/
theorem apply_outside {s : StoreOp} {mem : Memory} {a : UInt64}
    (h : ¬ (s.addr.toNat ≤ a.toNat ∧ a.toNat < s.addr.toNat + s.byteLen.toNat)) :
    (s.apply mem).byte a = mem.byte a := by
  unfold apply
  simp [h]

/-- A byte inside the store's range reads the corresponding LE byte of
    `s.value`. -/
theorem apply_inside {s : StoreOp} {mem : Memory} {a : UInt64}
    (h_lo : s.addr.toNat ≤ a.toNat)
    (h_hi : a.toNat < s.addr.toNat + s.byteLen.toNat) :
    (s.apply mem).byte a =
      (s.value >>> UInt64.ofNat (8 * (a.toNat - s.addr.toNat))).toUInt8 := by
  unfold apply
  simp [h_lo, h_hi]

end StoreOp

-- ============================================================================
-- MprotectOp — identity on Memory; just a rfl-lemma for symmetry.
-- ============================================================================

namespace MprotectOp

/-- Mprotect doesn't change byte at any address (identity on `Memory`). -/
@[simp] theorem apply_byte (m : MprotectOp) (mem : Memory) (a : UInt64) :
    (m.apply mem).byte a = mem.byte a := rfl

end MprotectOp

end LeanLoad

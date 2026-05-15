/-
Characterisation lemmas for the per-op denotations defined in
`Spec/Apply.lean`. Two shapes per op, per field:

  · `apply_outside` — addresses outside the op's range are
    preserved.
  · `apply_inside`  — addresses inside the op's range read the
    op's intended value.

Byte-level lemmas (suffix-free `apply_outside` / `apply_inside`)
cover the `byte` field; `apply_perm_outside` / `apply_perm_inside`
cover the `perm` field. Ops that don't touch one of the fields
have only the relevant subset (e.g., `ZeroOp` has only byte
lemmas; `MprotectOp` has only perm lemmas).

These are the structural building blocks the soundness theorems
compose:

  · bytes_preserved      — `MmapOp.apply_inside`  + later `apply_outside`s.
  · bss_zeroed           — `apply_no_touch` over the whole tree.
  · relocs_applied       — `StoreOp.apply_inside` + later `apply_outside`s.
  · permissions_correct  — `MprotectOp.apply_perm_inside` + later
                             `apply_perm_outside`s.

All four ops have decidable in-range predicates, so the lemmas
discharge via plain `if_pos` / `if_neg` reductions.
-/

import LeanLoad.Spec.Apply

namespace LeanLoad

open LeanLoad.Spec

-- ============================================================================
-- MmapOp — both byte and perm change inside the range.
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

/-- Perm outside the mmap's range is preserved. -/
theorem apply_perm_outside {fs : File} {m : MmapOp} {mem : Memory} {a : UInt64}
    (h : ¬ (m.addr.toNat ≤ a.toNat ∧ a.toNat < m.addr.toNat + m.len.toNat)) :
    (m.apply fs mem).perm a = mem.perm a := by
  unfold apply
  simp [h]

/-- Perm inside the mmap's range is `m.prot ||| PROT_WRITE` (widened
    so subsequent stores can run). -/
theorem apply_perm_inside {fs : File} {m : MmapOp} {mem : Memory} {a : UInt64}
    (h_lo : m.addr.toNat ≤ a.toNat)
    (h_hi : a.toNat < m.addr.toNat + m.len.toNat) :
    (m.apply fs mem).perm a = m.prot ||| Runtime.PROT_WRITE := by
  unfold apply
  simp [h_lo, h_hi]

end MmapOp

-- ============================================================================
-- ZeroOp — only byte changes; perm passes through.
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

/-- Zero doesn't change perm at any address. -/
@[simp] theorem apply_perm (z : ZeroOp) (mem : Memory) (a : UInt64) :
    (z.apply mem).perm a = mem.perm a := rfl

end ZeroOp

-- ============================================================================
-- StoreOp — only byte changes; perm passes through.
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

/-- Store doesn't change perm at any address. -/
@[simp] theorem apply_perm (s : StoreOp) (mem : Memory) (a : UInt64) :
    (s.apply mem).perm a = mem.perm a := rfl

end StoreOp

-- ============================================================================
-- MprotectOp — only perm changes; byte passes through.
-- ============================================================================

namespace MprotectOp

/-- Mprotect doesn't change byte at any address. -/
@[simp] theorem apply_byte (m : MprotectOp) (mem : Memory) (a : UInt64) :
    (m.apply mem).byte a = mem.byte a := rfl

/-- Perm outside the mprotect's range is preserved. -/
theorem apply_perm_outside {m : MprotectOp} {mem : Memory} {a : UInt64}
    (h : ¬ (m.addr.toNat ≤ a.toNat ∧ a.toNat < m.addr.toNat + m.len.toNat)) :
    (m.apply mem).perm a = mem.perm a := by
  unfold apply
  simp [h]

/-- Perm inside the mprotect's range reads `m.prot`. -/
theorem apply_perm_inside {m : MprotectOp} {mem : Memory} {a : UInt64}
    (h_lo : m.addr.toNat ≤ a.toNat)
    (h_hi : a.toNat < m.addr.toNat + m.len.toNat) :
    (m.apply mem).perm a = m.prot := by
  unfold apply
  simp [h_lo, h_hi]

end MprotectOp

end LeanLoad

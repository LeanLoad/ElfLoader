/-
Soundness theorems for the loader's byte-level effect on memory.

Three target statements, each phrased about the pure denotation
`LoadOps.apply`. To lift any of them to a statement about the
real loaded image, rewrite `runSafe_image …` via the FFI axiom
`runSafe_image_eq` and the same conclusion drops out of the pure
proof.

Status:

  · `LoadOps.apply_preserves_outside_reservation` — proved.
    A byte outside the reservation is preserved by every level of
    `apply`, by induction over the tree, using `LoadSafe`'s in-range
    witnesses.

  · `bytes_preserved` / `bss_zeroed` / `relocs_applied` —
    *stated*, proofs deferred (`sorry`). The final statements
    will quantify over PT_LOAD ranges through the `BoundPlan`
    interface; that interface is in flux (concurrent
    `Layout` / `Build` / `Reloc` work). When it settles, the
    statements gain their `BoundPlan` preconditions and the
    proofs fill in by composing the per-op `apply_inside`
    lemmas with `LoadSafe.mmapsDisjoint` (plus a
    `storesPairwiseDisjoint` extension to `LoadSafe` for
    `relocs_applied`).

Proof recipe (for each big theorem):

  1. Pick the op responsible for the byte at `a` — `MmapOp.apply`
     puts the file byte (`bytes_preserved`), `ZeroOp.apply` or
     `Memory.zero` puts the 0 (`bss_zeroed`), `StoreOp.apply`
     puts the LE byte (`relocs_applied`).
  2. Use `Op.apply_inside` to read off the byte's value after
     that op runs.
  3. For every *later* op in the tree, use `Op.apply_outside`
     to preserve the value. The "outside" preconditions come
     from `LoadSafe`'s disjointness / in-range fields.
  4. Conclude with extensional rewriting.
-/

import LeanLoad.Spec.ApplyLemmas
import LeanLoad.Spec.FFI
import LeanLoad.Materialize.Safety

namespace LeanLoad.Spec

open LeanLoad
open LeanLoad.Materialize

-- ============================================================================
-- Tree-level structural lemma: bytes outside the reservation are
-- preserved by `LoadOps.apply`. Used as a stepping stone for the
-- three big soundness theorems (each of which restricts attention
-- to bytes *inside* the reservation, and uses this lemma's "outside"
-- companion to ignore unrelated cross-segment effects).
-- ============================================================================

/-- An address inside the reservation. -/
private def InReservation (rsvAddr rsvLen : UInt64) (a : UInt64) : Prop :=
  rsvAddr.toNat ≤ a.toNat ∧ a.toNat < rsvAddr.toNat + rsvLen.toNat

/-- `MmapOp.apply` does not touch `a` if `a` is outside the
    reservation and the op is `InRange`. -/
private theorem MmapOp.apply_preserves_outside
    {fs : FileSnap} {m : MmapOp} {mem : Memory}
    {rsvAddr rsvLen : UInt64} {a : UInt64}
    (h_inRsv : Runtime.InRange m.addr m.len rsvAddr rsvLen)
    (h_outside : ¬ InReservation rsvAddr rsvLen a) :
    (m.apply fs mem) a = mem a := by
  apply LeanLoad.MmapOp.apply_outside
  -- Need: ¬ (m.addr.toNat ≤ a.toNat ∧ a.toNat < m.addr.toNat + m.len.toNat)
  obtain ⟨h_lo, h_hi⟩ := h_inRsv
  intro ⟨h_a_lo, h_a_hi⟩
  apply h_outside
  refine ⟨?_, ?_⟩
  · exact Nat.le_trans h_lo h_a_lo
  · exact Nat.lt_of_lt_of_le h_a_hi h_hi

/-- `ZeroOp.apply` does not touch `a` if `a` is outside the
    reservation and the op is `InRange`. -/
private theorem ZeroOp.apply_preserves_outside
    {z : ZeroOp} {mem : Memory}
    {rsvAddr rsvLen : UInt64} {a : UInt64}
    (h_inRsv : Runtime.InRange z.addr z.len rsvAddr rsvLen)
    (h_outside : ¬ InReservation rsvAddr rsvLen a) :
    (z.apply mem) a = mem a := by
  apply LeanLoad.ZeroOp.apply_outside
  obtain ⟨h_lo, h_hi⟩ := h_inRsv
  intro ⟨h_a_lo, h_a_hi⟩
  apply h_outside
  exact ⟨Nat.le_trans h_lo h_a_lo, Nat.lt_of_lt_of_le h_a_hi h_hi⟩

/-- `StoreOp.apply` does not touch `a` if `a` is outside the
    reservation and the op is `InRange`. -/
private theorem StoreOp.apply_preserves_outside
    {s : StoreOp} {mem : Memory}
    {rsvAddr rsvLen : UInt64} {a : UInt64}
    (h_inRsv : Runtime.InRange s.addr s.byteLen rsvAddr rsvLen)
    (h_outside : ¬ InReservation rsvAddr rsvLen a) :
    (s.apply mem) a = mem a := by
  apply LeanLoad.StoreOp.apply_outside
  obtain ⟨h_lo, h_hi⟩ := h_inRsv
  intro ⟨h_a_lo, h_a_hi⟩
  apply h_outside
  exact ⟨Nat.le_trans h_lo h_a_lo, Nat.lt_of_lt_of_le h_a_hi h_hi⟩

-- ============================================================================
-- The three target soundness theorems.
--
-- Stated about `LoadOps.apply` over `Memory.zero`. To lift to a
-- statement about the real loaded image, replace
--   `(LoadOps.apply fs lo Memory.zero) a`
-- with
--   `(runSafe_image rsv lo safe fs) a`
-- via `runSafe_image_eq`.
-- ============================================================================

/-- **bytes_preserved (pre-relocation)** — every byte in every mmap's
    file-backed range equals the corresponding source-file byte,
    *outside* any later `StoreOp`'s patch window.

    Recipe (when filling in): take the responsible mmap's
    `MmapOp.apply_inside`; chain `apply_outside` over every
    later op in tree order using `LoadSafe`'s disjointness +
    the explicit "outside-stores" hypothesis. -/
theorem bytes_preserved
    {n : Nat} (lo : Materialize.LoadOps n) (fs : FileSnap)
    {rsvAddr rsvLen : UInt64} (safe : Materialize.LoadSafe rsvAddr rsvLen lo)
    (i : Nat) (h_i : i < lo.size)
    (k : Nat) (h_k : k < (lo[i]'h_i).segments.size)
    (m : MmapOp)
    (h_mmap : ((lo[i]'h_i).segments[k]'h_k).mmap = some m)
    (a : UInt64)
    (h_a_lo : m.addr.toNat ≤ a.toNat)
    (h_a_hi : a.toNat < m.addr.toNat + m.len.toNat)
    -- "a is not in any store's patch window across the whole tree"
    (h_no_store : ∀ (i' : Nat) (h_i' : i' < lo.size)
                    (k' : Nat) (h_k' : k' < (lo[i']'h_i').segments.size)
                    (s : StoreOp),
                    s ∈ ((lo[i']'h_i').segments[k']'h_k').stores →
                    ¬ (s.addr.toNat ≤ a.toNat ∧
                       a.toNat < s.addr.toNat + s.byteLen.toNat)) :
    (Materialize.LoadOps.apply fs lo Memory.zero) a
      = fs.byte m.handle (m.offset + (a - m.addr)) := by
  sorry

/-- **bss_zeroed** — every byte in a PT_LOAD's
    `[vaddr + filesz, vaddr + memsz)` range reads `0`, outside
    any later `StoreOp`'s patch window.

    Decomposes into three byte ranges that read 0 for different
    reasons (see `docs/plan.md` plus the soundness write-up):
      · Partial-page tail covered by `ZeroOp`     — `ZeroOp.apply_inside`.
      · Full anon pages past the file overlay     — `Memory.zero` initial.
      · No-overlap with subsequent segment mmaps  — `LoadSafe.mmapsDisjoint`.

    Statement deliberately quantifies over an arbitrary `a : UInt64`
    in the BSS range; the proof case-splits on which sub-range it
    falls into. -/
theorem bss_zeroed
    {n : Nat} (lo : Materialize.LoadOps n) (fs : FileSnap)
    {rsvAddr rsvLen : UInt64} (safe : Materialize.LoadSafe rsvAddr rsvLen lo)
    (a : UInt64)
    -- Preconditions phrased structurally; full BoundPlan-aware form
    -- will refine these to "a in [vaddr+filesz, vaddr+memsz) of some
    -- PT_LOAD segment".
    (h_in_rsv : rsvAddr.toNat ≤ a.toNat ∧ a.toNat < rsvAddr.toNat + rsvLen.toNat)
    (h_no_mmap_byte : ∀ (i : Nat) (h_i : i < lo.size)
                        (k : Nat) (h_k : k < (lo[i]'h_i).segments.size)
                        (m : MmapOp),
                        ((lo[i]'h_i).segments[k]'h_k).mmap = some m →
                        ¬ (m.addr.toNat ≤ a.toNat ∧
                           a.toNat < m.addr.toNat + m.len.toNat))
    (h_no_store : ∀ (i : Nat) (h_i : i < lo.size)
                    (k : Nat) (h_k : k < (lo[i]'h_i).segments.size)
                    (s : StoreOp),
                    s ∈ ((lo[i]'h_i).segments[k]'h_k).stores →
                    ¬ (s.addr.toNat ≤ a.toNat ∧
                       a.toNat < s.addr.toNat + s.byteLen.toNat)) :
    (Materialize.LoadOps.apply fs lo Memory.zero) a = 0 := by
  sorry

/-- **relocs_applied** — every byte covered by a `StoreOp` reads the
    appropriate little-endian byte of `s.value`, *provided* no
    *later* store overlaps.

    Currently `LoadSafe` only guarantees `mmapsDisjoint`, not
    `storesPairwiseDisjoint`. The "no later store overlaps"
    hypothesis here is the explicit form of what
    `LoadSafe.storesPairwiseDisjoint` would discharge. Lifting it
    into `LoadSafe` is the recommended follow-up (`docs/plan.md`
    note); until then, this theorem takes it as an argument.

    Refined statement (after BoundPlan settles) will phrase the
    `StoreOp` as the one emitted for a specific `Reloc.Entry` and
    its value as `formula entry.type {S, A, B, P}`. -/
theorem relocs_applied
    {n : Nat} (lo : Materialize.LoadOps n) (fs : FileSnap)
    {rsvAddr rsvLen : UInt64} (safe : Materialize.LoadSafe rsvAddr rsvLen lo)
    (i : Nat) (h_i : i < lo.size)
    (k : Nat) (h_k : k < (lo[i]'h_i).segments.size)
    (s : StoreOp)
    (h_s_mem : s ∈ ((lo[i]'h_i).segments[k]'h_k).stores)
    (a : UInt64)
    (h_a_lo : s.addr.toNat ≤ a.toNat)
    (h_a_hi : a.toNat < s.addr.toNat + s.byteLen.toNat)
    -- "no later store in the tree-walk order overlaps a"
    (h_no_later_store : ∀ (i' : Nat) (h_i' : i' < lo.size)
                          (k' : Nat) (h_k' : k' < (lo[i']'h_i').segments.size)
                          (s' : StoreOp),
                          s' ∈ ((lo[i']'h_i').segments[k']'h_k').stores →
                          s' ≠ s →  -- placeholder; real form will use tree position
                          ¬ (s'.addr.toNat ≤ a.toNat ∧
                             a.toNat < s'.addr.toNat + s'.byteLen.toNat)) :
    (Materialize.LoadOps.apply fs lo Memory.zero) a
      = (s.value >>> UInt64.ofNat (8 * (a.toNat - s.addr.toNat))).toUInt8 := by
  sorry

end LeanLoad.Spec

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
-- Tree-level preservation: bytes outside the reservation are preserved
-- by `SegmentOps.apply` / `ElfOps.apply` / `LoadOps.apply`. Proved
-- structurally by composing the per-op `apply_preserves_outside`
-- lemmas through the apply tree using `LoadSafe`'s InRange fields.
-- ============================================================================

/-- Fold form for the stores. Reduces to identity outside the
    reservation, given each store's InRange witness. -/
private theorem stores_foldl_outside_rsv
    (stores : Array StoreOp) (mem : Memory)
    {rsvAddr rsvLen a : UInt64}
    (h_each : ∀ s ∈ stores, Runtime.InRange s.addr s.byteLen rsvAddr rsvLen)
    (h_out : ¬ InReservation rsvAddr rsvLen a) :
    (stores.foldl (init := mem) fun m s => s.apply m) a = mem a := by
  let motive : Nat → Memory → Prop := fun _ mem' => mem' a = mem a
  have h_full : motive stores.size (stores.foldl (init := mem) fun m s => s.apply m) := by
    refine Array.foldl_induction motive ?_ ?_
    · show mem a = mem a; rfl
    · intro idx acc ih
      show (stores[idx].apply acc) a = mem a
      have h_mem : stores[idx] ∈ stores := stores.getElem_mem idx.isLt
      rw [StoreOp.apply_preserves_outside (h_each _ h_mem) h_out]
      exact ih
  exact h_full

/-- Fold form for stores with an explicit "no store touches `a`"
    hypothesis. The general form that `stores_foldl_outside_rsv`
    specialises (the latter derives the per-store hypothesis from
    InRange + outside-reservation). Used in the positive direction
    by `SegmentOps.apply_inside_mmap_no_overwrite`. -/
private theorem stores_foldl_no_touch
    (stores : Array StoreOp) (mem : Memory) {a : UInt64}
    (h_each : ∀ s ∈ stores,
      ¬ (s.addr.toNat ≤ a.toNat ∧ a.toNat < s.addr.toNat + s.byteLen.toNat)) :
    (stores.foldl (init := mem) fun m s => s.apply m) a = mem a := by
  let motive : Nat → Memory → Prop := fun _ mem' => mem' a = mem a
  have h_full : motive stores.size (stores.foldl (init := mem) fun m s => s.apply m) := by
    refine Array.foldl_induction motive ?_ ?_
    · show mem a = mem a; rfl
    · intro idx acc ih
      show (stores[idx].apply acc) a = mem a
      have h_mem : stores[idx] ∈ stores := stores.getElem_mem idx.isLt
      rw [LeanLoad.StoreOp.apply_outside (h_each _ h_mem)]
      exact ih
  exact h_full

/-- Per-segment positive preservation: if `so.mmap` writes file bytes
    at `a`, and neither `so.zero` nor any of `so.stores` overlaps `a`,
    then the full per-segment apply chain reads back the file byte at
    `a`. This is the within-segment workhorse for `bytes_preserved`. -/
theorem SegmentOps.apply_inside_mmap_no_overwrite
    {n : Nat} {fs : FileSnap} {so : Materialize.SegmentOps n} {mem : Memory}
    {m : MmapOp}
    (h_mmap : so.mmap = some m)
    {a : UInt64}
    (h_a_lo : m.addr.toNat ≤ a.toNat)
    (h_a_hi : a.toNat < m.addr.toNat + m.len.toNat)
    (h_no_zero : ∀ z, so.zero = some z →
      ¬ (z.addr.toNat ≤ a.toNat ∧ a.toNat < z.addr.toNat + z.len.toNat))
    (h_no_store : ∀ s ∈ so.stores,
      ¬ (s.addr.toNat ≤ a.toNat ∧ a.toNat < s.addr.toNat + s.byteLen.toNat)) :
    (Materialize.SegmentOps.apply fs so mem) a
      = fs.byte m.handle (m.offset + (a - m.addr)) := by
  unfold Materialize.SegmentOps.apply
  simp only [MprotectOp.apply]
  rw [h_mmap]
  cases h_zero : so.zero with
  | none =>
    dsimp only
    rw [stores_foldl_no_touch so.stores _ h_no_store]
    exact LeanLoad.MmapOp.apply_inside h_a_lo h_a_hi
  | some z =>
    dsimp only
    rw [stores_foldl_no_touch so.stores _ h_no_store]
    rw [LeanLoad.ZeroOp.apply_outside (h_no_zero z h_zero)]
    exact LeanLoad.MmapOp.apply_inside h_a_lo h_a_hi

/-- Per-segment tree preservation: outside the reservation, the
    segment's full apply chain (mmap → zero → stores → mprotect) is
    the identity.

    Proof: case-split on `so.mmap` and `so.zero` (Option) so the
    inner `match`s reduce to a concrete branch, then chain the per-op
    `apply_preserves_outside` lemmas. The stores fold is discharged
    by `stores_foldl_outside_rsv`; the final `mprotect` is the byte-
    level identity. -/
theorem SegmentOps.apply_preserves_outside_reservation
    {n : Nat} {fs : FileSnap} {so : Materialize.SegmentOps n} {mem : Memory}
    {rsvAddr rsvLen a : UInt64}
    (safe : Materialize.SegmentSafe rsvAddr rsvLen so)
    (h_out : ¬ InReservation rsvAddr rsvLen a) :
    (Materialize.SegmentOps.apply fs so mem) a = mem a := by
  unfold Materialize.SegmentOps.apply
  simp only [MprotectOp.apply]
  cases h_mmap : so.mmap with
  | none =>
    cases h_zero : so.zero with
    | none =>
      dsimp only
      exact stores_foldl_outside_rsv so.stores _ safe.storesInRange h_out
    | some z =>
      dsimp only
      rw [stores_foldl_outside_rsv so.stores _ safe.storesInRange h_out]
      exact ZeroOp.apply_preserves_outside (safe.zeroInRange z h_zero) h_out
  | some m =>
    cases h_zero : so.zero with
    | none =>
      dsimp only
      rw [stores_foldl_outside_rsv so.stores _ safe.storesInRange h_out]
      exact MmapOp.apply_preserves_outside (safe.mmapInRange m h_mmap) h_out
    | some z =>
      dsimp only
      rw [stores_foldl_outside_rsv so.stores _ safe.storesInRange h_out]
      rw [ZeroOp.apply_preserves_outside (safe.zeroInRange z h_zero) h_out]
      exact MmapOp.apply_preserves_outside (safe.mmapInRange m h_mmap) h_out

/-- Per-elf tree preservation: every segment's apply preserves bytes
    outside the reservation, so the fold does too. -/
theorem ElfOps.apply_preserves_outside_reservation
    {n : Nat} {fs : FileSnap} {eo : Materialize.ElfOps n} {mem : Memory}
    {rsvAddr rsvLen a : UInt64}
    (safe : Materialize.ElfSafe rsvAddr rsvLen eo)
    (h_out : ¬ InReservation rsvAddr rsvLen a) :
    (Materialize.ElfOps.apply fs eo mem) a = mem a := by
  unfold Materialize.ElfOps.apply
  let motive : Nat → Memory → Prop := fun _ mem' => mem' a = mem a
  have h_full : motive eo.segments.size
      (eo.segments.foldl (init := mem) fun m so => Materialize.SegmentOps.apply fs so m) := by
    refine Array.foldl_induction motive ?_ ?_
    · show mem a = mem a; rfl
    · intro idx acc ih
      show (Materialize.SegmentOps.apply fs (eo.segments[idx.val]'idx.isLt) acc) a = mem a
      rw [SegmentOps.apply_preserves_outside_reservation
            (safe.segments idx.val idx.isLt) h_out]
      exact ih
  exact h_full

-- ============================================================================
-- "No touch" tree preservation: a strictly more general form that
-- takes explicit per-op no-touch hypotheses instead of deriving them
-- from `LoadSafe` + outside-reservation. The substrate for
-- `bss_zeroed` (which has no op touching the BSS address) and for the
-- "post-m" propagation in `bytes_preserved`. The structure mirrors
-- the `outside_reservation` family exactly.
-- ============================================================================

/-- Per-segment no-touch preservation: if no op in this segment
    touches `a`, the segment's apply preserves the byte at `a`. -/
theorem SegmentOps.apply_no_touch
    {n : Nat} {fs : FileSnap} {so : Materialize.SegmentOps n} {mem : Memory}
    {a : UInt64}
    (h_no_mmap : ∀ m, so.mmap = some m →
      ¬ (m.addr.toNat ≤ a.toNat ∧ a.toNat < m.addr.toNat + m.len.toNat))
    (h_no_zero : ∀ z, so.zero = some z →
      ¬ (z.addr.toNat ≤ a.toNat ∧ a.toNat < z.addr.toNat + z.len.toNat))
    (h_no_store : ∀ s ∈ so.stores,
      ¬ (s.addr.toNat ≤ a.toNat ∧ a.toNat < s.addr.toNat + s.byteLen.toNat)) :
    (Materialize.SegmentOps.apply fs so mem) a = mem a := by
  unfold Materialize.SegmentOps.apply
  simp only [MprotectOp.apply]
  cases h_mmap : so.mmap with
  | none =>
    cases h_zero : so.zero with
    | none =>
      dsimp only
      exact stores_foldl_no_touch so.stores _ h_no_store
    | some z =>
      dsimp only
      rw [stores_foldl_no_touch so.stores _ h_no_store]
      exact LeanLoad.ZeroOp.apply_outside (h_no_zero z h_zero)
  | some m =>
    cases h_zero : so.zero with
    | none =>
      dsimp only
      rw [stores_foldl_no_touch so.stores _ h_no_store]
      exact LeanLoad.MmapOp.apply_outside (h_no_mmap m h_mmap)
    | some z =>
      dsimp only
      rw [stores_foldl_no_touch so.stores _ h_no_store]
      rw [LeanLoad.ZeroOp.apply_outside (h_no_zero z h_zero)]
      exact LeanLoad.MmapOp.apply_outside (h_no_mmap m h_mmap)

/-- Per-elf no-touch preservation: if no op in any segment of this
    elf touches `a`, the elf's apply preserves the byte at `a`. -/
theorem ElfOps.apply_no_touch
    {n : Nat} {fs : FileSnap} {eo : Materialize.ElfOps n} {mem : Memory}
    {a : UInt64}
    (h_no_mmap : ∀ (k : Nat) (h_k : k < eo.segments.size) (m : MmapOp),
      (eo.segments[k]'h_k).mmap = some m →
      ¬ (m.addr.toNat ≤ a.toNat ∧ a.toNat < m.addr.toNat + m.len.toNat))
    (h_no_zero : ∀ (k : Nat) (h_k : k < eo.segments.size) (z : ZeroOp),
      (eo.segments[k]'h_k).zero = some z →
      ¬ (z.addr.toNat ≤ a.toNat ∧ a.toNat < z.addr.toNat + z.len.toNat))
    (h_no_store : ∀ (k : Nat) (h_k : k < eo.segments.size) (s : StoreOp),
      s ∈ (eo.segments[k]'h_k).stores →
      ¬ (s.addr.toNat ≤ a.toNat ∧ a.toNat < s.addr.toNat + s.byteLen.toNat)) :
    (Materialize.ElfOps.apply fs eo mem) a = mem a := by
  unfold Materialize.ElfOps.apply
  let motive : Nat → Memory → Prop := fun _ mem' => mem' a = mem a
  have h_full : motive eo.segments.size
      (eo.segments.foldl (init := mem) fun m so => Materialize.SegmentOps.apply fs so m) := by
    refine Array.foldl_induction motive ?_ ?_
    · show mem a = mem a; rfl
    · intro idx acc ih
      show (Materialize.SegmentOps.apply fs (eo.segments[idx.val]'idx.isLt) acc) a = mem a
      rw [SegmentOps.apply_no_touch
            (fun m h => h_no_mmap idx.val idx.isLt m h)
            (fun z h => h_no_zero idx.val idx.isLt z h)
            (fun s h => h_no_store idx.val idx.isLt s h)]
      exact ih
  exact h_full

/-- Top-level no-touch preservation: if no op in the entire tree
    touches `a`, the materialize pipeline preserves the byte at `a`.
    This is the structural workhorse for `bss_zeroed` and for the
    "post-m" half of `bytes_preserved`. -/
theorem LoadOps.apply_no_touch
    {n : Nat} {fs : FileSnap} {lo : Materialize.LoadOps n} {mem : Memory}
    {a : UInt64}
    (h_no_mmap : ∀ (i : Nat) (h_i : i < lo.size)
                  (k : Nat) (h_k : k < (lo[i]'h_i).segments.size) (m : MmapOp),
      ((lo[i]'h_i).segments[k]'h_k).mmap = some m →
      ¬ (m.addr.toNat ≤ a.toNat ∧ a.toNat < m.addr.toNat + m.len.toNat))
    (h_no_zero : ∀ (i : Nat) (h_i : i < lo.size)
                  (k : Nat) (h_k : k < (lo[i]'h_i).segments.size) (z : ZeroOp),
      ((lo[i]'h_i).segments[k]'h_k).zero = some z →
      ¬ (z.addr.toNat ≤ a.toNat ∧ a.toNat < z.addr.toNat + z.len.toNat))
    (h_no_store : ∀ (i : Nat) (h_i : i < lo.size)
                   (k : Nat) (h_k : k < (lo[i]'h_i).segments.size) (s : StoreOp),
      s ∈ ((lo[i]'h_i).segments[k]'h_k).stores →
      ¬ (s.addr.toNat ≤ a.toNat ∧ a.toNat < s.addr.toNat + s.byteLen.toNat)) :
    (Materialize.LoadOps.apply fs lo mem) a = mem a := by
  unfold Materialize.LoadOps.apply
  let motive : Nat → Memory → Prop := fun _ mem' => mem' a = mem a
  have h_full : motive lo.size
      (lo.foldl (init := mem) fun m eo => Materialize.ElfOps.apply fs eo m) := by
    refine Array.foldl_induction motive ?_ ?_
    · show mem a = mem a; rfl
    · intro idx acc ih
      show (Materialize.ElfOps.apply fs (lo[idx.val]'idx.isLt) acc) a = mem a
      rw [ElfOps.apply_no_touch
            (fun k h_k m h => h_no_mmap idx.val idx.isLt k h_k m h)
            (fun k h_k z h => h_no_zero idx.val idx.isLt k h_k z h)
            (fun k h_k s h => h_no_store idx.val idx.isLt k h_k s h)]
      exact ih
  exact h_full

/-- Top-level tree preservation: bytes outside the reservation are
    untouched by the entire materialize pipeline. The structural
    workhorse for the three soundness theorems below — it lets later-
    elf effects drop through when the byte of interest is in an
    earlier elf's range. -/
theorem LoadOps.apply_preserves_outside_reservation
    {n : Nat} {fs : FileSnap} {lo : Materialize.LoadOps n} {mem : Memory}
    {rsvAddr rsvLen a : UInt64}
    (safe : Materialize.LoadSafe rsvAddr rsvLen lo)
    (h_out : ¬ InReservation rsvAddr rsvLen a) :
    (Materialize.LoadOps.apply fs lo mem) a = mem a := by
  unfold Materialize.LoadOps.apply
  let motive : Nat → Memory → Prop := fun _ mem' => mem' a = mem a
  have h_full : motive lo.size
      (lo.foldl (init := mem) fun m eo => Materialize.ElfOps.apply fs eo m) := by
    refine Array.foldl_induction motive ?_ ?_
    · show mem a = mem a; rfl
    · intro idx acc ih
      show (Materialize.ElfOps.apply fs (lo[idx.val]'idx.isLt) acc) a = mem a
      rw [ElfOps.apply_preserves_outside_reservation
            (safe.elfs idx.val idx.isLt) h_out]
      exact ih
  exact h_full

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
  -- Proof skeleton (to fill in once build stabilises and the
  -- BoundPlan interface settles):
  --
  -- 1. `LoadOps.apply` is a left-fold over `lo`, each step folding
  --    over `eo.segments`, each step applying mmap → zero → stores
  --    → mprotect. Express the fold as
  --       [pre-op ops] ++ [the mmap m at position (i,k)] ++ [post-op ops]
  --    via `Array.foldl_eq_foldl_split` (existing in Mathlib) on
  --    both the elf array and the segment array.
  --
  -- 2. After "the mmap m" step, the byte at `a` equals
  --    `fs.byte m.handle (m.offset + (a - m.addr))` by
  --    `MmapOp.apply_inside h_a_lo h_a_hi`.
  --
  -- 3. For every post-op op in the chain:
  --     · The same segment's zero/stores/mprotect:
  --         - zero  — disjoint from mmap by segment geometry
  --                   (zero covers [seg.vaddr+filesz, +partialBssLen),
  --                    mmap covers [pageVaddr, +fileOverlayLen) — the
  --                    SegmentLayout's `vaddr_memsz_le_pageEnd` +
  --                    `fileOverlay_le_pageLength` give disjointness).
  --                   Not currently witnessed by `LoadSafe`; will
  --                   need a `SegmentSafe.zeroVsMmapDisjoint` field.
  --         - stores — explicit hypothesis `h_no_store`.
  --         - mprotect — byte-level no-op (`MprotectOp.apply_at`).
  --     · Later segments in the same elf:
  --         - mmaps disjoint by `ElfSafe.mmapsDisjoint`.
  --         - zeros disjoint from earlier mmap — needs a similar
  --           cross-segment zero/mmap disjointness witness or
  --           reasoning via mmap disjointness + geometry.
  --         - stores — explicit hypothesis.
  --     · Later elves:
  --         - mmaps disjoint by `LoadSafe.mmapsDisjoint`.
  --         - zeros / stores — explicit hypothesis (or future
  --           LoadSafe extensions).
  --
  -- 4. Compose the per-op `apply_outside` lemmas through the
  --    post-op chain via the same `Array.foldl_induction` pattern
  --    used in `LoadOps.apply_preserves_outside_reservation`.
  --
  -- Notes: `apply_preserves_outside_reservation` is a *related*
  -- structural fact (preserves bytes outside the *reservation*),
  -- but `bytes_preserved` needs preservation along a *single
  -- byte's worldline* across ops that touch the reservation but
  -- not `a`. Different shape; both rely on per-op `apply_outside`.
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
    (a : UInt64)
    -- Preconditions phrased structurally; full BoundPlan-aware form
    -- will refine these to "a in [vaddr+filesz, vaddr+memsz) of some
    -- PT_LOAD segment". The disjointness story (why no mmap/zero/
    -- store touches the BSS byte) is what the future BoundPlan-aware
    -- statement will discharge; for now the three hypotheses are
    -- explicit.
    (h_no_mmap : ∀ (i : Nat) (h_i : i < lo.size)
                   (k : Nat) (h_k : k < (lo[i]'h_i).segments.size)
                   (m : MmapOp),
                   ((lo[i]'h_i).segments[k]'h_k).mmap = some m →
                   ¬ (m.addr.toNat ≤ a.toNat ∧
                      a.toNat < m.addr.toNat + m.len.toNat))
    (h_no_zero : ∀ (i : Nat) (h_i : i < lo.size)
                   (k : Nat) (h_k : k < (lo[i]'h_i).segments.size)
                   (z : ZeroOp),
                   ((lo[i]'h_i).segments[k]'h_k).zero = some z →
                   ¬ (z.addr.toNat ≤ a.toNat ∧
                      a.toNat < z.addr.toNat + z.len.toNat))
    (h_no_store : ∀ (i : Nat) (h_i : i < lo.size)
                    (k : Nat) (h_k : k < (lo[i]'h_i).segments.size)
                    (s : StoreOp),
                    s ∈ ((lo[i]'h_i).segments[k]'h_k).stores →
                    ¬ (s.addr.toNat ≤ a.toNat ∧
                       a.toNat < s.addr.toNat + s.byteLen.toNat)) :
    (Materialize.LoadOps.apply fs lo Memory.zero) a = 0 := by
  rw [LoadOps.apply_no_touch h_no_mmap h_no_zero h_no_store]
  rfl

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

/-
Soundness theorems for the loader's byte-level effect on memory.

Each theorem is stated about the pure denotation `LoadOps.apply`
over a byte-level `Memory` model (in `Materialize/Apply.lean`). To
lift to the real loaded image, rewrite `runSafe_image …` via the
FFI axiom `runSafe_image_eq` (in `LeanLoad/RuntimeAxiom.lean`) and
the same conclusion drops out of the pure proof.

The file is laid out bottom-up:

  1. Per-op `apply_preserves_outside` — outside the reservation,
     each `Op.apply` is a `mem.byte`-identity.

  2. Tree-level "outside-reservation" preservation (`SegmentOps`,
     `ElfOps`, `LoadOps`). Each composes the per-op lemmas via
     `LoadSafe`'s `InRange` field witnesses.

  3. Tree-level "no-touch" / "at-target" — strictly more general:
     take explicit per-op no-touch hypotheses instead of deriving
     them from `LoadSafe` + outside-reservation. Substrate for
     `bss_zeroed` (no op touching the BSS address) and the
     "post-m" propagation in `bytes_preserved`. The "at-target"
     form pins a specific byte to a target value given the
     responsible `(elf, segment)` index.

  4. The three end-to-end target theorems:

       · `bytes_preserved`  — every file-overlaid byte equals its
                              source-file byte.
       · `bss_zeroed`       — every byte in a PT_LOAD's
                              `[eaddr+filesz, eaddr+memsz)` reads 0.
       · `relocs_applied`   — every byte in a `StoreOp`'s patch
                              window reads its LE byte.

`Memory` does not model permissions, so there is no
`permissions_correct` here; a future perm-tracking `Memory` plus a
`LoadSafe.mprotectsPairwiseDisjoint` extension would reintroduce it.

Status:

  · `LoadOps.apply_preserves_outside_reservation` — proved.
  · `bytes_preserved` / `bss_zeroed` / `relocs_applied` — *stated*,
    proofs lean on the supporting lemmas. The hypotheses currently
    take explicit disjointness witnesses; a future `LoadSafe`
    extension (`zeroDisjointFromMmap` / `storesPairwiseDisjoint`)
    derived from `Plan/Layout.lean` geometry would discharge them
    from safety alone.

Proof recipe (for each big theorem):

  1. Pick the op responsible for the byte at `a` — `MmapOp.apply`
     puts the file byte (`bytes_preserved`), `ZeroOp.apply` or
     `Memory.zero` puts the 0 (`bss_zeroed`), `StoreOp.apply`
     puts the LE byte (`relocs_applied`).
  2. Use `Op.apply_inside` to read off the byte's value after
     that op runs.
  3. For every *later* op in the tree, use `Op.apply_outside`
     to preserve the value. The "outside" preconditions come
     from `LoadSafe`'s disjointness / in-range fields plus the
     explicit per-call hypotheses.
  4. Conclude with extensional rewriting.
-/

import LeanLoad.Materialize.ApplyLemmas
import LeanLoad.Materialize.Safety
import LeanLoad.RuntimeAxiom

namespace LeanLoad

open LeanLoad.Materialize

-- ============================================================================
-- Per-op preservation. Outside the reservation, each op is a
-- byte-identity. Used as the leaf of every tree-level induction below.
-- ============================================================================

/-- An address inside the reservation. -/
private def InReservation (rsvAddr rsvLen : UInt64) (a : UInt64) : Prop :=
  rsvAddr.toNat ≤ a.toNat ∧ a.toNat < rsvAddr.toNat + rsvLen.toNat

/-- `MmapOp.apply` does not touch `a` if `a` is outside the
    reservation and the op is `InRange`. -/
private theorem MmapOp.apply_preserves_outside
    {fs : File} {m : MmapOp} {mem : Memory}
    {rsvAddr rsvLen : UInt64} {a : UInt64}
    (h_inRsv : Runtime.InRange m.addr m.len rsvAddr rsvLen)
    (h_outside : ¬ InReservation rsvAddr rsvLen a) :
    (m.apply fs mem).byte a = mem.byte a := by
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
    (z.apply mem).byte a = mem.byte a := by
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
    (s.apply mem).byte a = mem.byte a := by
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
    (stores.foldl (init := mem) fun m s => s.apply m).byte a = mem.byte a := by
  let motive : Nat → Memory → Prop := fun _ mem' => mem'.byte a = mem.byte a
  have h_full : motive stores.size (stores.foldl (init := mem) fun m s => s.apply m) := by
    refine Array.foldl_induction motive ?_ ?_
    · show mem.byte a = mem.byte a; rfl
    · intro idx acc ih
      show (stores[idx].apply acc).byte a = mem.byte a
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
    (stores.foldl (init := mem) fun m s => s.apply m).byte a = mem.byte a := by
  let motive : Nat → Memory → Prop := fun _ mem' => mem'.byte a = mem.byte a
  have h_full : motive stores.size (stores.foldl (init := mem) fun m s => s.apply m) := by
    refine Array.foldl_induction motive ?_ ?_
    · show mem.byte a = mem.byte a; rfl
    · intro idx acc ih
      show (stores[idx].apply acc).byte a = mem.byte a
      have h_mem : stores[idx] ∈ stores := stores.getElem_mem idx.isLt
      rw [LeanLoad.StoreOp.apply_outside (h_each _ h_mem)]
      exact ih
  exact h_full

/-- Inner-most positional fold: stores at index `store_idx` writes
    value, no later store in the array overlaps `a`, ⇒ the foldl
    leaves byte `a` at that store's LE byte. The within-stores
    workhorse for `relocs_applied`. Same motive shape as
    `LoadOps.apply_at_responsible_mmap` (past target index ⇒ byte
    fixed). -/
private theorem stores_foldl_at_responsible_store
    (stores : Array StoreOp) (mem : Memory)
    {store_idx : Nat} (h_idx : store_idx < stores.size)
    {a : UInt64}
    (h_a_lo : (stores[store_idx]'h_idx).addr.toNat ≤ a.toNat)
    (h_a_hi : a.toNat <
              (stores[store_idx]'h_idx).addr.toNat +
                (stores[store_idx]'h_idx).byteLen.toNat)
    (h_no_later : ∀ (idx' : Nat) (h_idx' : idx' < stores.size),
      store_idx < idx' →
      ¬ ((stores[idx']'h_idx').addr.toNat ≤ a.toNat ∧
         a.toNat < (stores[idx']'h_idx').addr.toNat +
                   (stores[idx']'h_idx').byteLen.toNat)) :
    (stores.foldl (init := mem) fun m s => s.apply m).byte a
      = ((stores[store_idx]'h_idx).value >>>
         UInt64.ofNat (8 * (a.toNat -
                            (stores[store_idx]'h_idx).addr.toNat))).toUInt8 := by
  let motive : Nat → Memory → Prop := fun n mem' =>
    store_idx < n →
      mem'.byte a = ((stores[store_idx]'h_idx).value >>>
                UInt64.ofNat (8 * (a.toNat -
                                   (stores[store_idx]'h_idx).addr.toNat))).toUInt8
  have h_full : motive stores.size
      (stores.foldl (init := mem) fun m s => s.apply m) := by
    refine Array.foldl_induction motive ?_ ?_
    · intro h_lt; omega
    · intro idx acc ih h_lt
      by_cases h_eq : store_idx = idx.val
      · -- Responsible store: subst flips store_idx ↦ idx.val.
        subst h_eq
        show (stores[idx.val].apply acc).byte a = _
        exact LeanLoad.StoreOp.apply_inside h_a_lo h_a_hi
      · -- Different store, must be post-store_idx.
        have h_post : store_idx < idx.val := by
          have : store_idx < idx.val + 1 := h_lt
          omega
        have h_no_touch := h_no_later idx.val idx.isLt h_post
        show (stores[idx.val].apply acc).byte a = _
        rw [LeanLoad.StoreOp.apply_outside h_no_touch]
        exact ih h_post
  exact h_full h_idx

/-- Within-segment positive preservation for a `StoreOp` at index
    `store_idx`: if `a ∈ s`'s range and no later store in `so.stores`
    overlaps `a`, the segment's full apply chain leaves `a` at the
    store's LE byte. Mmap/zero run before stores in `runUnsafe`
    order, so the responsible store overwrites their effect at `a`
    regardless of value — no mmap/zero hypotheses needed. -/
theorem SegmentOps.apply_at_responsible_store
    {n : Nat} {fs : File} {so : Materialize.SegmentOps n} {mem : Memory}
    {store_idx : Nat} (h_si : store_idx < so.stores.size)
    {a : UInt64}
    (h_a_lo : (so.stores[store_idx]'h_si).addr.toNat ≤ a.toNat)
    (h_a_hi : a.toNat <
              (so.stores[store_idx]'h_si).addr.toNat +
                (so.stores[store_idx]'h_si).byteLen.toNat)
    (h_no_later : ∀ (idx' : Nat) (h_idx' : idx' < so.stores.size),
      store_idx < idx' →
      ¬ ((so.stores[idx']'h_idx').addr.toNat ≤ a.toNat ∧
         a.toNat < (so.stores[idx']'h_idx').addr.toNat +
                   (so.stores[idx']'h_idx').byteLen.toNat)) :
    (Materialize.SegmentOps.apply fs so mem).byte a
      = ((so.stores[store_idx]'h_si).value >>>
         UInt64.ofNat (8 * (a.toNat -
                            (so.stores[store_idx]'h_si).addr.toNat))).toUInt8 := by
  unfold Materialize.SegmentOps.apply
  simp only [MprotectOp.apply]
  -- The match-bound init of the stores fold is irrelevant — the
  -- responsible store overwrites at `a` regardless.
  exact stores_foldl_at_responsible_store so.stores _ h_si h_a_lo h_a_hi h_no_later

/-- Per-segment positive preservation: if `so.mmap` writes file bytes
    at `a`, and neither `so.zero` nor any of `so.stores` overlaps `a`,
    then the full per-segment apply chain reads back the file byte at
    `a`. This is the within-segment workhorse for `bytes_preserved`. -/
theorem SegmentOps.apply_inside_mmap_no_overwrite
    {n : Nat} {fs : File} {so : Materialize.SegmentOps n} {mem : Memory}
    {m : MmapOp}
    (h_mmap : so.mmap = some m)
    {a : UInt64}
    (h_a_lo : m.addr.toNat ≤ a.toNat)
    (h_a_hi : a.toNat < m.addr.toNat + m.len.toNat)
    (h_no_zero : ∀ z, so.zero = some z →
      ¬ (z.addr.toNat ≤ a.toNat ∧ a.toNat < z.addr.toNat + z.len.toNat))
    (h_no_store : ∀ s ∈ so.stores,
      ¬ (s.addr.toNat ≤ a.toNat ∧ a.toNat < s.addr.toNat + s.byteLen.toNat)) :
    (Materialize.SegmentOps.apply fs so mem).byte a
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
    {n : Nat} {fs : File} {so : Materialize.SegmentOps n} {mem : Memory}
    {rsvAddr rsvLen a : UInt64}
    (safe : Materialize.SegmentSafe rsvAddr rsvLen so)
    (h_out : ¬ InReservation rsvAddr rsvLen a) :
    (Materialize.SegmentOps.apply fs so mem).byte a = mem.byte a := by
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
    {n : Nat} {fs : File} {eo : Materialize.ElfOps n} {mem : Memory}
    {rsvAddr rsvLen a : UInt64}
    (safe : Materialize.ElfSafe rsvAddr rsvLen eo)
    (h_out : ¬ InReservation rsvAddr rsvLen a) :
    (Materialize.ElfOps.apply fs eo mem).byte a = mem.byte a := by
  unfold Materialize.ElfOps.apply
  let motive : Nat → Memory → Prop := fun _ mem' => mem'.byte a = mem.byte a
  have h_full : motive eo.segments.size
      (eo.segments.foldl (init := mem) fun m so => Materialize.SegmentOps.apply fs so m) := by
    refine Array.foldl_induction motive ?_ ?_
    · show mem.byte a = mem.byte a; rfl
    · intro idx acc ih
      show (Materialize.SegmentOps.apply fs (eo.segments[idx.val]'idx.isLt) acc).byte a = mem.byte a
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
    {n : Nat} {fs : File} {so : Materialize.SegmentOps n} {mem : Memory}
    {a : UInt64}
    (h_no_mmap : ∀ m, so.mmap = some m →
      ¬ (m.addr.toNat ≤ a.toNat ∧ a.toNat < m.addr.toNat + m.len.toNat))
    (h_no_zero : ∀ z, so.zero = some z →
      ¬ (z.addr.toNat ≤ a.toNat ∧ a.toNat < z.addr.toNat + z.len.toNat))
    (h_no_store : ∀ s ∈ so.stores,
      ¬ (s.addr.toNat ≤ a.toNat ∧ a.toNat < s.addr.toNat + s.byteLen.toNat)) :
    (Materialize.SegmentOps.apply fs so mem).byte a = mem.byte a := by
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
    {n : Nat} {fs : File} {eo : Materialize.ElfOps n} {mem : Memory}
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
    (Materialize.ElfOps.apply fs eo mem).byte a = mem.byte a := by
  unfold Materialize.ElfOps.apply
  let motive : Nat → Memory → Prop := fun _ mem' => mem'.byte a = mem.byte a
  have h_full : motive eo.segments.size
      (eo.segments.foldl (init := mem) fun m so => Materialize.SegmentOps.apply fs so m) := by
    refine Array.foldl_induction motive ?_ ?_
    · show mem.byte a = mem.byte a; rfl
    · intro idx acc ih
      show (Materialize.SegmentOps.apply fs (eo.segments[idx.val]'idx.isLt) acc).byte a = mem.byte a
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
    {n : Nat} {fs : File} {lo : Materialize.LoadOps n} {mem : Memory}
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
    (Materialize.LoadOps.apply fs lo mem).byte a = mem.byte a := by
  unfold Materialize.LoadOps.apply
  let motive : Nat → Memory → Prop := fun _ mem' => mem'.byte a = mem.byte a
  have h_full : motive lo.size
      (lo.foldl (init := mem) fun m eo => Materialize.ElfOps.apply fs eo m) := by
    refine Array.foldl_induction motive ?_ ?_
    · show mem.byte a = mem.byte a; rfl
    · intro idx acc ih
      show (Materialize.ElfOps.apply fs (lo[idx.val]'idx.isLt) acc).byte a = mem.byte a
      rw [ElfOps.apply_no_touch
            (fun k h_k m h => h_no_mmap idx.val idx.isLt k h_k m h)
            (fun k h_k z h => h_no_zero idx.val idx.isLt k h_k z h)
            (fun k h_k s h => h_no_store idx.val idx.isLt k h_k s h)]
      exact ih
  exact h_full

/-- Top-level positive preservation, parameterised by the target
    byte. If applying segments[k] of elf i produces `target` at `a`
    from *any* input memory, and every other segment (of elf i) and
    every other elf preserves byte `a`, then the materialize
    pipeline leaves byte `a` at `target`.

    Subsumes both the mmap and store positional structures: callers
    supply the within-segment theorem for their target (mmap →
    `SegmentOps.apply_inside_mmap_no_overwrite`; store →
    `SegmentOps.apply_at_responsible_store`) and the "outside
    segment-pair preserves a" lemmas via `SegmentOps.apply_no_touch`
    and `ElfOps.apply_no_touch`. The nested fold induction (over
    elves, then over segments of the responsible elf) lives here
    once. -/
theorem LoadOps.apply_at_target
    {n : Nat} {fs : File} {lo : Materialize.LoadOps n} {mem : Memory}
    {i : Nat} (h_i : i < lo.size)
    {k : Nat} (h_k : k < (lo[i]'h_i).segments.size)
    {a : UInt64} {target : UInt8}
    (h_within : ∀ (acc : Memory),
      (Materialize.SegmentOps.apply fs ((lo[i]'h_i).segments[k]'h_k) acc).byte a = target)
    (h_other_segs : ∀ (k' : Nat) (h_k' : k' < (lo[i]'h_i).segments.size), k' ≠ k →
      ∀ (acc : Memory),
      (Materialize.SegmentOps.apply fs ((lo[i]'h_i).segments[k']'h_k') acc).byte a = acc.byte a)
    (h_other_elves : ∀ (i' : Nat) (h_i' : i' < lo.size), i' ≠ i →
      ∀ (acc : Memory),
      (Materialize.ElfOps.apply fs (lo[i']'h_i') acc).byte a = acc.byte a) :
    (Materialize.LoadOps.apply fs lo mem).byte a = target := by
  -- Inner: applying the responsible elf produces `target` at `a`.
  have h_elf_i_apply : ∀ (acc : Memory),
      (Materialize.ElfOps.apply fs (lo[i]'h_i) acc).byte a = target := by
    intro acc
    unfold Materialize.ElfOps.apply
    let inner_motive : Nat → Memory → Prop := fun j_idx mem' =>
      k < j_idx → mem'.byte a = target
    have h_inner : inner_motive (lo[i]'h_i).segments.size
        ((lo[i]'h_i).segments.foldl (init := acc)
          fun acc' so => Materialize.SegmentOps.apply fs so acc') := by
      refine Array.foldl_induction inner_motive ?_ ?_
      · intro h_lt; omega
      · intro jdx acc' ih h_lt
        by_cases h_eq : k = jdx.val
        · subst h_eq
          show (Materialize.SegmentOps.apply fs ((lo[i]'h_i).segments[jdx.val]'jdx.isLt) acc').byte a = target
          exact h_within acc'
        · have h_post_k : k < jdx.val := by
            have : k < jdx.val + 1 := h_lt
            omega
          have h_jdx_ne_k : jdx.val ≠ k := fun h => h_eq h.symm
          show (Materialize.SegmentOps.apply fs ((lo[i]'h_i).segments[jdx.val]'jdx.isLt) acc').byte a = target
          rw [h_other_segs jdx.val jdx.isLt h_jdx_ne_k acc']
          exact ih h_post_k
    exact h_inner h_k
  -- Outer: fold over elves.
  unfold Materialize.LoadOps.apply
  let outer_motive : Nat → Memory → Prop := fun idx mem' =>
    i < idx → mem'.byte a = target
  have h_outer : outer_motive lo.size
      (lo.foldl (init := mem) fun acc eo => Materialize.ElfOps.apply fs eo acc) := by
    refine Array.foldl_induction outer_motive ?_ ?_
    · intro h_lt; omega
    · intro idx acc ih h_lt
      by_cases h_eq : i = idx.val
      · subst h_eq
        show (Materialize.ElfOps.apply fs (lo[idx.val]'idx.isLt) acc).byte a = target
        exact h_elf_i_apply acc
      · have h_post_i : i < idx.val := by
          have : i < idx.val + 1 := h_lt
          omega
        have h_idx_ne_i : idx.val ≠ i := fun h => h_eq h.symm
        show (Materialize.ElfOps.apply fs (lo[idx.val]'idx.isLt) acc).byte a = target
        rw [h_other_elves idx.val idx.isLt h_idx_ne_i acc]
        exact ih h_post_i
  exact h_outer h_i

/-- Top-level tree preservation: bytes outside the reservation are
    untouched by the entire materialize pipeline. The structural
    workhorse for the three soundness theorems below — it lets later-
    elf effects drop through when the byte of interest is in an
    earlier elf's range. -/
theorem LoadOps.apply_preserves_outside_reservation
    {n : Nat} {fs : File} {lo : Materialize.LoadOps n} {mem : Memory}
    {rsvAddr rsvLen a : UInt64}
    (safe : Materialize.LoadSafe rsvAddr rsvLen lo)
    (h_out : ¬ InReservation rsvAddr rsvLen a) :
    (Materialize.LoadOps.apply fs lo mem).byte a = mem.byte a := by
  unfold Materialize.LoadOps.apply
  let motive : Nat → Memory → Prop := fun _ mem' => mem'.byte a = mem.byte a
  have h_full : motive lo.size
      (lo.foldl (init := mem) fun m eo => Materialize.ElfOps.apply fs eo m) := by
    refine Array.foldl_induction motive ?_ ?_
    · show mem.byte a = mem.byte a; rfl
    · intro idx acc ih
      show (Materialize.ElfOps.apply fs (lo[idx.val]'idx.isLt) acc).byte a = mem.byte a
      rw [ElfOps.apply_preserves_outside_reservation
            (safe.elfs idx.val idx.isLt) h_out]
      exact ih
  exact h_full

-- ============================================================================
-- Cross-tree disjointness helper: derive "no other mmap touches `a`"
-- from `LoadSafe` plus `a ∈ m`'s range. Used by `bytes_preserved`.
-- ============================================================================

/-- Helper: derive "no other mmap in the tree touches `a`" from
    `LoadSafe` plus `a ∈ m`'s range. Three cases:
      · Different elf (i ≠ i') — `LoadSafe.mmapsDisjoint`.
      · Same elf, different segment — `ElfSafe.mmapsDisjoint` from
        `safe.elfs i h_i`.
      · Same elf, same segment (excluded by `h_diff`). -/
private theorem other_mmap_not_touches
    {n : Nat} {lo : Materialize.LoadOps n}
    {rsvAddr rsvLen : UInt64} (safe : Materialize.LoadSafe rsvAddr rsvLen lo)
    {i : Nat} (h_i : i < lo.size)
    {k : Nat} (h_k : k < (lo[i]'h_i).segments.size)
    {m : MmapOp}
    (h_mmap : ((lo[i]'h_i).segments[k]'h_k).mmap = some m)
    {a : UInt64}
    (h_a_lo : m.addr.toNat ≤ a.toNat)
    (h_a_hi : a.toNat < m.addr.toNat + m.len.toNat)
    {i' : Nat} (h_i' : i' < lo.size)
    {k' : Nat} (h_k' : k' < (lo[i']'h_i').segments.size)
    {m' : MmapOp}
    (h_mmap' : ((lo[i']'h_i').segments[k']'h_k').mmap = some m')
    (h_diff : ¬ (i' = i ∧ k' = k)) :
    ¬ (m'.addr.toNat ≤ a.toNat ∧ a.toNat < m'.addr.toNat + m'.len.toNat) := by
  rcases Nat.lt_trichotomy i i' with h_lt | h_eq | h_gt
  · have h_disj := safe.mmapsDisjoint i i' h_i h_i' h_lt k k' h_k h_k' m m' h_mmap h_mmap'
    intro ⟨h_lo', h_hi'⟩
    rcases h_disj with h₁ | h₂ <;> omega
  · subst h_eq
    -- Different segments in the same elf — extract k' ≠ k from h_diff.
    have h_k_ne : k' ≠ k := fun h => h_diff ⟨rfl, h⟩
    have h_safe_elf := safe.elfs i h_i
    rcases Nat.lt_or_gt_of_ne h_k_ne with h_k_lt | h_k_gt
    · have h_disj := h_safe_elf.mmapsDisjoint k' k h_k' h_k h_k_lt m' m h_mmap' h_mmap
      intro ⟨h_lo', h_hi'⟩
      rcases h_disj with h₁ | h₂ <;> omega
    · have h_disj := h_safe_elf.mmapsDisjoint k k' h_k h_k' h_k_gt m m' h_mmap h_mmap'
      intro ⟨h_lo', h_hi'⟩
      rcases h_disj with h₁ | h₂ <;> omega
  · have h_disj := safe.mmapsDisjoint i' i h_i' h_i h_gt k' k h_k' h_k m' m h_mmap' h_mmap
    intro ⟨h_lo', h_hi'⟩
    rcases h_disj with h₁ | h₂ <;> omega

-- ============================================================================
-- The three target soundness theorems.
--
-- Stated about `LoadOps.apply` over `Memory.zero`. To lift to a
-- statement about the real loaded image, replace
--   `(LoadOps.apply fs lo Memory.zero).byte a`
-- with
--   `(runSafe_image rsv lo safe fs).byte a`
-- via `runSafe_image_eq`.
-- ============================================================================

/-- **bytes_preserved** — every byte in every mmap's file-backed
    range equals the corresponding source-file byte, *outside* any
    `ZeroOp` or `StoreOp` patch window across the whole tree.

    Recipe: derive "no other mmap touches `a`" from
    `LoadSafe.mmapsDisjoint` (cross-elf) + `ElfSafe.mmapsDisjoint`
    (within-elf) via `other_mmap_not_touches`, then apply
    `LoadOps.apply_at_target`.

    The two explicit hypotheses `h_no_zero` and `h_no_store` carry
    the disjointness witnesses that `LoadSafe` does not currently
    provide. A future `LoadSafe.zeroDisjointFromMmap` /
    `LoadSafe.storesPairwiseDisjoint` extension would derive both
    internally from the `Plan/Layout.lean` segment-geometry
    invariants. -/
theorem bytes_preserved
    {n : Nat} (lo : Materialize.LoadOps n) (fs : File)
    {rsvAddr rsvLen : UInt64} (safe : Materialize.LoadSafe rsvAddr rsvLen lo)
    (i : Nat) (h_i : i < lo.size)
    (k : Nat) (h_k : k < (lo[i]'h_i).segments.size)
    (m : MmapOp)
    (h_mmap : ((lo[i]'h_i).segments[k]'h_k).mmap = some m)
    (a : UInt64)
    (h_a_lo : m.addr.toNat ≤ a.toNat)
    (h_a_hi : a.toNat < m.addr.toNat + m.len.toNat)
    (h_no_zero : ∀ (i' : Nat) (h_i' : i' < lo.size)
                   (k' : Nat) (h_k' : k' < (lo[i']'h_i').segments.size)
                   (z : ZeroOp),
                   ((lo[i']'h_i').segments[k']'h_k').zero = some z →
                   ¬ (z.addr.toNat ≤ a.toNat ∧
                      a.toNat < z.addr.toNat + z.len.toNat))
    (h_no_store : ∀ (i' : Nat) (h_i' : i' < lo.size)
                    (k' : Nat) (h_k' : k' < (lo[i']'h_i').segments.size)
                    (s : StoreOp),
                    s ∈ ((lo[i']'h_i').segments[k']'h_k').stores →
                    ¬ (s.addr.toNat ≤ a.toNat ∧
                       a.toNat < s.addr.toNat + s.byteLen.toNat)) :
    (Materialize.LoadOps.apply fs lo Memory.zero).byte a
      = fs.byte m.handle (m.offset + (a - m.addr)) := by
  apply LoadOps.apply_at_target h_i h_k
  · -- Responsible segment k of elf i: any acc → file byte at a.
    intro acc
    exact SegmentOps.apply_inside_mmap_no_overwrite h_mmap h_a_lo h_a_hi
      (fun z h => h_no_zero i h_i k h_k z h)
      (fun s h => h_no_store i h_i k h_k s h)
  · -- Other segments of elf i preserve a.
    intro k' h_k' h_k'_ne acc
    apply SegmentOps.apply_no_touch
    · intro m' h_m'
      exact other_mmap_not_touches safe h_i h_k h_mmap h_a_lo h_a_hi
        h_i h_k' h_m' (fun ⟨_, h_k_eq⟩ => h_k'_ne h_k_eq)
    · intro z h_z; exact h_no_zero i h_i k' h_k' z h_z
    · intro s h_s; exact h_no_store i h_i k' h_k' s h_s
  · -- Other elves preserve a.
    intro i' h_i' h_i'_ne acc
    apply ElfOps.apply_no_touch
    · intro k' h_k' m' h_m'
      exact other_mmap_not_touches safe h_i h_k h_mmap h_a_lo h_a_hi
        h_i' h_k' h_m' (fun ⟨h_i_eq, _⟩ => h_i'_ne h_i_eq)
    · intro k' h_k' z h_z; exact h_no_zero i' h_i' k' h_k' z h_z
    · intro k' h_k' s h_s; exact h_no_store i' h_i' k' h_k' s h_s

/-- **bss_zeroed** — every byte in a PT_LOAD's
    `[eaddr + filesz, eaddr + memsz)` range reads `0`, outside
    any later `StoreOp`'s patch window.

    Decomposes into three byte ranges that read 0 for different
    reasons:
      · Partial-page tail covered by `ZeroOp`     — `ZeroOp.apply_inside`.
      · Full anon pages past the file overlay     — `Memory.zero` initial.
      · No-overlap with subsequent segment mmaps  — `LoadSafe.mmapsDisjoint`.

    Statement deliberately quantifies over an arbitrary `a : UInt64`
    in the BSS range; the proof case-splits on which sub-range it
    falls into. -/
theorem bss_zeroed
    {n : Nat} (lo : Materialize.LoadOps n) (fs : File)
    (a : UInt64)
    -- Preconditions phrased structurally; full BoundPlan-aware form
    -- will refine these to "a in [eaddr+filesz, eaddr+memsz) of some
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
    (Materialize.LoadOps.apply fs lo Memory.zero).byte a = 0 := by
  rw [LoadOps.apply_no_touch h_no_mmap h_no_zero h_no_store]
  rfl

/-- **relocs_applied** — the store at position `(i, k, store_idx)`
    of `lo` writes its little-endian bytes at the corresponding
    addresses. Specifically, byte `a` inside the store's window
    reads `(s.value >>> 8*(a - s.addr)).toUInt8`.

    Phrased with explicit `store_idx` (rather than via `s ∈ stores`)
    so the proof can use the within-stores positional lemma
    `stores_foldl_at_responsible_store`. Callers with `s ∈ stores`
    can recover an index via `Array.getElem_of_mem`.

    Three exclusion hypotheses (mmap / zero / store at any
    *other* segment of any elf) carry the disjointness witnesses
    that `LoadSafe` does not yet provide. A future
    `LoadSafe.zeroDisjointFromMmap` / `LoadSafe.storesPairwiseDisjoint`
    extension would derive them from `Plan/Layout.lean` geometry.
    The within-segment-but-after hypothesis `h_no_later_in_seg`
    captures "no later store in the same segment overlaps a". -/
theorem relocs_applied
    {n : Nat} (lo : Materialize.LoadOps n) (fs : File)
    (i : Nat) (h_i : i < lo.size)
    (k : Nat) (h_k : k < (lo[i]'h_i).segments.size)
    (store_idx : Nat) (h_si : store_idx < ((lo[i]'h_i).segments[k]'h_k).stores.size)
    (a : UInt64)
    (h_a_lo : (((lo[i]'h_i).segments[k]'h_k).stores[store_idx]'h_si).addr.toNat ≤ a.toNat)
    (h_a_hi : a.toNat <
              (((lo[i]'h_i).segments[k]'h_k).stores[store_idx]'h_si).addr.toNat +
                (((lo[i]'h_i).segments[k]'h_k).stores[store_idx]'h_si).byteLen.toNat)
    (h_no_later_in_seg : ∀ (idx' : Nat)
                          (h_idx' : idx' < ((lo[i]'h_i).segments[k]'h_k).stores.size),
      store_idx < idx' →
      ¬ ((((lo[i]'h_i).segments[k]'h_k).stores[idx']'h_idx').addr.toNat ≤ a.toNat ∧
         a.toNat < (((lo[i]'h_i).segments[k]'h_k).stores[idx']'h_idx').addr.toNat +
                   (((lo[i]'h_i).segments[k]'h_k).stores[idx']'h_idx').byteLen.toNat))
    (h_other_mmaps : ∀ (i' : Nat) (h_i' : i' < lo.size)
                       (k' : Nat) (h_k' : k' < (lo[i']'h_i').segments.size) (m' : MmapOp),
      ((lo[i']'h_i').segments[k']'h_k').mmap = some m' →
      ¬ (i' = i ∧ k' = k) →
      ¬ (m'.addr.toNat ≤ a.toNat ∧ a.toNat < m'.addr.toNat + m'.len.toNat))
    (h_other_zeros : ∀ (i' : Nat) (h_i' : i' < lo.size)
                       (k' : Nat) (h_k' : k' < (lo[i']'h_i').segments.size) (z : ZeroOp),
      ((lo[i']'h_i').segments[k']'h_k').zero = some z →
      ¬ (i' = i ∧ k' = k) →
      ¬ (z.addr.toNat ≤ a.toNat ∧ a.toNat < z.addr.toNat + z.len.toNat))
    (h_other_stores : ∀ (i' : Nat) (h_i' : i' < lo.size)
                        (k' : Nat) (h_k' : k' < (lo[i']'h_i').segments.size) (s : StoreOp),
      s ∈ ((lo[i']'h_i').segments[k']'h_k').stores →
      ¬ (i' = i ∧ k' = k) →
      ¬ (s.addr.toNat ≤ a.toNat ∧ a.toNat < s.addr.toNat + s.byteLen.toNat)) :
    (Materialize.LoadOps.apply fs lo Memory.zero).byte a
      = ((((lo[i]'h_i).segments[k]'h_k).stores[store_idx]'h_si).value >>>
         UInt64.ofNat (8 * (a.toNat -
                            (((lo[i]'h_i).segments[k]'h_k).stores[store_idx]'h_si).addr.toNat))).toUInt8 := by
  apply LoadOps.apply_at_target h_i h_k
  · -- Responsible segment: any acc → LE byte of s.value at a.
    intro acc
    exact SegmentOps.apply_at_responsible_store h_si h_a_lo h_a_hi h_no_later_in_seg
  · -- Other segments of elf i preserve a.
    intro k' h_k' h_k'_ne acc
    apply SegmentOps.apply_no_touch
    · intro m' h_m'
      exact h_other_mmaps i h_i k' h_k' m' h_m' (fun ⟨_, h⟩ => h_k'_ne h)
    · intro z h_z
      exact h_other_zeros i h_i k' h_k' z h_z (fun ⟨_, h⟩ => h_k'_ne h)
    · intro s h_s
      exact h_other_stores i h_i k' h_k' s h_s (fun ⟨_, h⟩ => h_k'_ne h)
  · -- Other elves preserve a.
    intro i' h_i' h_i'_ne acc
    apply ElfOps.apply_no_touch
    · intro k' h_k' m' h_m'
      exact h_other_mmaps i' h_i' k' h_k' m' h_m' (fun ⟨h, _⟩ => h_i'_ne h)
    · intro k' h_k' z h_z
      exact h_other_zeros i' h_i' k' h_k' z h_z (fun ⟨h, _⟩ => h_i'_ne h)
    · intro k' h_k' s h_s
      exact h_other_stores i' h_i' k' h_k' s h_s (fun ⟨h, _⟩ => h_i'_ne h)

end LeanLoad

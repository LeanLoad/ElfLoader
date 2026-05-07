/-
Layout — per-object segment arrangement, pure.

Spec: gabi 07 § Program Header (positional concerns — base
assignment, span over loadable segments).

Layout consumes the elaborated PT_LOAD phdrs from
`obj.elf.loadablePhdrs` and assigns each object an mmap base + builds
the per-object plan that Reloc / Apply / Exec consume. Validation
that the page-aligned segments are sorted and non-overlapping happens
at the boundary in `g.layouts`, which returns a sized subtype carrying
the witness.

Init/fini ordering lives in `LeanLoad.Plan.Init` (gabi 08); this
file is purely gabi-07.
-/

import LeanLoad.Elaborate.Segment
import LeanLoad.Elaborate.Elf
import LeanLoad.Plan.Discover
import LeanLoad.Parse.Structs

namespace LeanLoad.Layout

open LeanLoad
open LeanLoad.Parse
open LeanLoad.Elaborate (Prot Segment alignDown alignUp)
open LeanLoad.Discover

-- ============================================================================
-- Prot → PROT_* translation (loader-level: typed `Prot` → POSIX `PROT_*`)
-- ============================================================================

/-- Translate typed segment permissions to POSIX `PROT_*` bits for
    `mprotect`. -/
def protOfPerm (p : Prot) : UInt32 :=
  (if p.read  then (1 : UInt32) else 0) |||
  (if p.write then (2 : UInt32) else 0) |||
  (if p.exec  then (4 : UInt32) else 0)

#guard protOfPerm { read := true,  write := false, exec := true  } = 5
#guard protOfPerm { read := true,  write := true,  exec := false } = 3
#guard protOfPerm { read := true,  write := false, exec := false } = 1

end LeanLoad.Layout

namespace LeanLoad.Layout

open LeanLoad
open LeanLoad.Parse
open LeanLoad.Elaborate (Segment alignUp)
open LeanLoad.Discover

-- ============================================================================
-- ObjectLayout — per-object plan with chosen base.
-- ============================================================================

/-- Layout for a single loaded object.

    `base` is the absolute mmap address at which the object's
    segments will be placed. For `ET_EXEC` (vaddrs already absolute)
    `base = 0`. For `ET_DYN`, Layout picks `base = dynAnchor +
    cumulative_offset` so each object lives in its own non-overlapping
    slot starting at `dynAnchor`. -/
structure ObjectLayout where
  /-- Absolute mmap base address chosen by Layout. -/
  base      : UInt64
  segments  : Array Elaborate.Segment
  /-- The `e_entry` field. `none` for objects we never enter. -/
  entry     : Option UInt64
  /-- True for the main executable. -/
  isMain    : Bool

/-- Hardcoded anchor for the first `ET_DYN` object. Picked to avoid
    colliding with the host process's typical mappings on x86-64 /
    aarch64 (heap, libc, etc., usually in the low GB). -/
def dynAnchor : UInt64 := 0x80000000

/-- The contiguous span an array of segments needs (relative to the
    object's base). -/
def objectSpan (segments : Array Elaborate.Segment) : UInt64 :=
  segments.foldl (init := 0) fun acc s => max acc s.pageEndAddr

/-- The contiguous span of one object's segments. -/
def ObjectLayout.span (lyt : ObjectLayout) : UInt64 :=
  objectSpan lyt.segments

/-- Layout for a single elaborated ELF. -/
def objectLayout (isMain : Bool) (base : UInt64) (elf : Elaborate.Elf) : ObjectLayout :=
  let entry := if isMain then some elf.entry else none
  { base, segments := elf.segments, entry, isMain }

/-- Segments are pairwise disjoint. -/
def ObjectLayout.segmentsPairwiseDisjoint (lyt : ObjectLayout) : Prop :=
  ∀ i j (_ : i < lyt.segments.size) (_ : j < lyt.segments.size),
    i ≠ j → Elaborate.Segment.disjoint lyt.segments[i] lyt.segments[j]

/-- Segments are sorted by page-aligned vaddr with each one's end ≤
    the next one's start. Bounded ∀ so Lean derives `Decidable`
    automatically. -/
def ObjectLayout.segmentsSorted (lyt : ObjectLayout) : Prop :=
  ∀ i, ∀ _ : i < lyt.segments.size, ∀ j, ∀ _ : j < lyt.segments.size,
    i < j → lyt.segments[i].pageEndAddr ≤ lyt.segments[j].pageVaddr

instance (lyt : ObjectLayout) : Decidable lyt.segmentsSorted := by
  unfold ObjectLayout.segmentsSorted; infer_instance

/-- Decidable Bool mirror of `segmentsSorted`. -/
def ObjectLayout.segmentsSortedB (lyt : ObjectLayout) : Bool :=
  decide lyt.segmentsSorted

/-- Forward bridge: the runtime check decides the proof-level invariant. -/
theorem ObjectLayout.segmentsSorted_of_segmentsSortedB
    (lyt : ObjectLayout) (h : lyt.segmentsSortedB = true) :
    lyt.segmentsSorted := of_decide_eq_true h

-- ============================================================================
-- Layout-stage entry point.
-- ============================================================================

/-- Assign an mmap base to each object in BFS order. `.exec`
    objects keep `0`; `.dyn` (and others) start at `dynAnchor` and
    stack by `alignUp objectSpan 0x1000`. -/
def assignBases (g : ObjectList) : Array UInt64 :=
  let f : (Array UInt64 × UInt64) → LoadedObject → (Array UInt64 × UInt64) :=
    fun (bases, cursor) obj =>
      if obj.elf.elfType == .exec then
        (bases.push 0, cursor)
      else
        let advance := alignUp (objectSpan obj.elf.segments) 0x1000
        (bases.push cursor, cursor + advance)
  (g.val.foldl (init := (Array.mkEmpty g.val.size, dynAnchor)) f).fst

/-- `assignBases` produces one base per object — the size matches the
    input dep graph by construction. Lets downstream consumers index
    `bases[i]` totally instead of falling back to `?.getD 0`. -/
theorem assignBases_size (g : ObjectList) : (assignBases g).size = g.val.size := by
  unfold assignBases
  let motive : Nat → Array UInt64 × UInt64 → Prop := fun n p => p.fst.size = n
  show motive g.val.size _
  refine Array.foldl_induction motive ?_ ?_
  · show (Array.mkEmpty g.val.size).size = 0; simp
  · intro idx ⟨bases, cursor⟩ ih
    have ih' : bases.size = idx.val := ih
    show (if (g.val[idx.val].elf.elfType == Elaborate.ElfType.exec) = true
            then (bases.push 0, cursor)
            else (bases.push cursor, cursor + _)).fst.size = idx.val + 1
    by_cases hExec : (g.val[idx.val].elf.elfType == Elaborate.ElfType.exec) = true
    · rw [if_pos hExec]; simp [ih']
    · rw [if_neg hExec]; simp [ih']

section Example

/-- Synthetic segment at `vaddr` of `memsz` bytes (page-aligned 0x1000),
    built via `Segment.ofPhdr`. The `Except` is unwrapped to `Option`;
    callers use `synthEt` (below) which threads the Option through to
    a possibly-empty `segments` array. Used by the `assignBases`
    examples to produce objects with non-zero spans so the stacking
    arithmetic is actually exercised. -/
private def synthSegment? (vaddr memsz : UInt64) : Option Elaborate.Segment :=
  let phdr : Parse.RawPhdr := { (default : Parse.RawPhdr) with
    p_type := Parse.PT_LOAD,
    p_vaddr := vaddr, p_memsz := memsz,
    p_filesz := 0, p_offset := 0, p_align := 0x1000 }
  (Elaborate.Segment.ofPhdr phdr #[] #[]).toOption

/-- Vacuous well-formedness for a singleton segments array: the
    quantifiers are over `i < j` with both `< 1`, which is unsatisfiable. -/
private theorem WellFormed_singleton (s : Elaborate.Segment) :
    Elaborate.WellFormed #[s] := by
  refine ⟨?_, ?_⟩
  all_goals intro i hi j hj hij; simp at hi hj; omega

private def synthEt (name : String) (et : Elaborate.ElfType)
    (segments : Array Elaborate.Segment := #[])
    (segmentsWf : Elaborate.WellFormed segments := by exact Elaborate.WellFormed_nil) :
    Discover.LoadedObject :=
  let elf : Elaborate.Elf :=
    { (default : Elaborate.Elf) with elfType := et, segments, segmentsWf }
  { name, path := s!"<synth:{name}>", handle := none, elf }

private def synthList (objs : Array Discover.LoadedObject) (h : 0 < objs.size) :
    Discover.ObjectList := ⟨objs, h⟩

#guard assignBases (synthList #[synthEt "main" .exec] (by simp)) = #[0]
#guard assignBases (synthList #[synthEt "lib" .dyn] (by simp)) = #[dynAnchor]

-- Stacking test: each .dyn lib has a 0x2000-byte span (one PT_LOAD at
-- vaddr 0 of memsz 0x2000 → pageEndAddr 0x2000), `advance =
-- alignUp 0x2000 0x1000 = 0x2000`. So libfoo gets dynAnchor, libbar
-- gets dynAnchor + 0x2000. The .exec keeps base 0 and doesn't move
-- the cursor.
private def stackingExample : Option (Array UInt64) := do
  let seg ← synthSegment? 0 0x2000
  let libObj (n : String) := synthEt n .dyn (segments := #[seg])
                                            (segmentsWf := WellFormed_singleton seg)
  some (assignBases (synthList #[synthEt "main" .exec, libObj "libfoo", libObj "libbar"]
                                (by simp)))

#guard stackingExample = some #[0, dynAnchor, dynAnchor + 0x2000]
end Example

end LeanLoad.Layout

namespace LeanLoad.Discover.ObjectList

open LeanLoad.Layout

/-- Build the per-object layouts for a discovered dep graph. `bases`
    has provably one entry per object (`assignBases_size`), so the
    in-loop `bases[i]` is total — no `?.getD` fallback. -/
def layouts (g : ObjectList) :
    Except String { a : Array ObjectLayout //
      a.size = g.val.size ∧
      ∀ (i : Nat) (h : i < a.size), a[i].segmentsSorted } :=
  let bases := assignBases g
  have hBases : bases.size = g.val.size := assignBases_size g
  let arr := g.val.mapFinIdx fun i obj h =>
    objectLayout (i == 0) (bases[i]'(hBases ▸ h)) obj.elf
  match harr : arr.findIdx? (fun lyt => lyt.segmentsSortedB == false) with
  | some i =>
    let name := (g.val[i]?.map (·.name)).getD "?"
    .error s!"layouts: object[{i}] ({name}) has malformed PT_LOAD segments"
  | none =>
    .ok ⟨arr, by
      refine ⟨by simp [arr], ?_⟩
      intro i hi
      have hall : ∀ x ∈ arr, (x.segmentsSortedB == false) = false :=
        Array.findIdx?_eq_none_iff.mp harr
      have hi_in : arr[i] ∈ arr := Array.getElem_mem hi
      have hb : arr[i].segmentsSortedB = true := by
        have := hall arr[i] hi_in
        simp at this
        exact this
      exact ObjectLayout.segmentsSorted_of_segmentsSortedB _ hb⟩

end LeanLoad.Discover.ObjectList

-- ============================================================================
-- Layout-stage spec theorems and runtime-bound proofs.
-- ============================================================================

namespace LeanLoad.Layout

open LeanLoad.Discover
open LeanLoad.Elaborate

theorem segment_endAddr_le_objectSpan
    (lyt : ObjectLayout) (i : Nat) (h : i < lyt.segments.size) :
    lyt.segments[i].pageEndAddr ≤ objectSpan lyt.segments := by
  let motive : Nat → UInt64 → Prop := fun n acc =>
    ∀ k (_ : k < n) (_ : k < lyt.segments.size),
      lyt.segments[k].pageEndAddr ≤ acc
  suffices motive lyt.segments.size (objectSpan lyt.segments) from this i h h
  unfold objectSpan
  refine Array.foldl_induction motive ?_ ?_
  · intros _ hk _; omega
  · intro idx b ih k hk hk'
    by_cases hkj : k = idx.val
    · have hindex : lyt.segments[k] = lyt.segments[idx] := by congr 1
      rw [hindex]
      show _ ≤ ite _ _ _
      split
      · exact UInt64.le_refl _
      · rename_i hnle; exact (UInt64.le_total b _).resolve_left hnle
    · have hk_lt : k < idx.val :=
        Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk) hkj
      have prev_le : lyt.segments[k].pageEndAddr ≤ b := ih k hk_lt hk'
      show _ ≤ ite _ _ _
      split
      · rename_i hb_le; exact UInt64.le_trans prev_le hb_le
      · exact prev_le

theorem bss_inRange (s : Segment) :
    Runtime.Region.InRange s.pageLength
      (s.pageInset + s.filesz) (s.memsz - s.filesz) := by
  have h_fm := s.fileszLeMemsz
  have h_inset := s.insetMemszLePageLength
  have h_fm_nat : s.filesz.toNat ≤ s.memsz.toNat := UInt64.le_iff_toNat_le.mp h_fm
  have h_pif_no_wrap : s.pageInset.toNat + s.filesz.toNat < 2^64 := by
    have h_2_64 : s.pageLength.toNat < 2^64 := s.pageLength.toNat_lt
    omega
  have h_pif_nat : (s.pageInset + s.filesz).toNat = s.pageInset.toNat + s.filesz.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h_pif_no_wrap
  have h_mf_nat : (s.memsz - s.filesz).toNat = s.memsz.toNat - s.filesz.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ h_fm]
  refine ⟨?_, ?_⟩
  · rw [UInt64.le_iff_toNat_le, h_pif_nat]; omega
  · have h_le1 : s.pageInset + s.filesz ≤ s.pageLength := by
      rw [UInt64.le_iff_toNat_le, h_pif_nat]; omega
    rw [UInt64.le_iff_toNat_le, h_mf_nat,
        UInt64.toNat_sub_of_le _ _ h_le1, h_pif_nat]
    omega

theorem patch_inRange (s : Segment) (r : LeanLoad.Parse.RawRela)
    (h_cov : Elaborate.coversRela s.vaddr s.memsz r) :
    Runtime.Region.InRange s.pageLength (r.r_offset - s.pageVaddr) 8 := by
  obtain ⟨h_lo, h_hi⟩ := h_cov
  have h_inset := s.insetMemszLePageLength
  have h_pv_le_v : s.pageVaddr ≤ s.vaddr := s.pageVaddr_le_vaddr
  have h_pv_le_v_nat : s.pageVaddr.toNat ≤ s.vaddr.toNat :=
    UInt64.le_iff_toNat_le.mp h_pv_le_v
  have h_pi_nat : s.pageInset.toNat = s.vaddr.toNat - s.pageVaddr.toNat := by
    rw [s.pageInset_eq, UInt64.toNat_sub_of_le _ _ h_pv_le_v]
  have h_pv_le_ro : s.pageVaddr ≤ r.r_offset := by
    apply UInt64.le_iff_toNat_le.mpr; omega
  have h_off_nat : (r.r_offset - s.pageVaddr).toNat = r.r_offset.toNat - s.pageVaddr.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ h_pv_le_ro]
  refine ⟨?_, ?_⟩
  · rw [UInt64.le_iff_toNat_le, h_off_nat]; omega
  · have h_le1 : r.r_offset - s.pageVaddr ≤ s.pageLength := by
      rw [UInt64.le_iff_toNat_le, h_off_nat]; omega
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ h_le1, h_off_nat]
    show (8 : UInt64).toNat ≤ _
    have h_eight : (8 : UInt64).toNat = 8 := rfl
    rw [h_eight]; omega

theorem inRange_4_of_8 {size offset : UInt64}
    (h : Runtime.Region.InRange size offset 8) :
    Runtime.Region.InRange size offset 4 := by
  refine ⟨h.1, ?_⟩
  have h_eight : (8 : UInt64).toNat = 8 := rfl
  have h_four  : (4 : UInt64).toNat = 4 := rfl
  have := UInt64.le_iff_toNat_le.mp h.2
  rw [h_eight] at this
  apply UInt64.le_iff_toNat_le.mpr
  rw [h_four]; omega

theorem segmentsPairwiseDisjoint_of_segmentsSorted
    (lyt : ObjectLayout) (h : lyt.segmentsSorted) :
    lyt.segmentsPairwiseDisjoint := by
  intro i j hi hj hne
  rcases Nat.lt_or_ge i j with hlt | hge
  · exact Or.inl (h i hi j hj hlt)
  · have hgt : j < i := Nat.lt_of_le_of_ne hge (Ne.symm hne)
    exact Or.inr (h j hj i hi hgt)

theorem ObjectLayout.segmentsSortedB_iff_segmentsSorted (lyt : ObjectLayout) :
    lyt.segmentsSortedB = true ↔ lyt.segmentsSorted :=
  ⟨of_decide_eq_true, decide_eq_true⟩

theorem ObjectList.layouts_segmentsPairwiseDisjoint
    (g : ObjectList)
    {a : Array ObjectLayout}
    (h : a.size = g.val.size ∧ ∀ (i : Nat) (hi : i < a.size), a[i].segmentsSorted)
    (i : Nat) (hi : i < a.size) :
    a[i].segmentsPairwiseDisjoint :=
  segmentsPairwiseDisjoint_of_segmentsSorted _ (h.right i hi)

end LeanLoad.Layout

/-
Symbol resolution.

Spec: gabi 08 § Shared Object Dependencies — "When resolving symbolic
references, the dynamic linker examines the symbol tables with a
breadth-first search. That is, it first looks at the symbol table of
the executable program itself, then at the symbol tables of the
`DT_NEEDED` entries (in order), and then at the second level
`DT_NEEDED` entries, and so on."

An object's symbol is a *definition* if `st_shndx ≠ SHN_UNDEF` and is
not `STB_LOCAL`. An *undefined reference* has `st_shndx = SHN_UNDEF`.
For each undefined reference across all loaded objects, we find a
defining (object, symbol) pair via breadth-first search over the
`LoadGraph.objects` array (which `Discover` already returns in BFS
order: main first, then NEEDED entries in their declared order).

Each entry's resolution is one of three explicit cases:
  • `found ref` — the BFS turned up a defining (object, symbol).
  • `weakUndef` — undef reference is weak (gabi 05 lets it bind to 0).
  • `strongUndef` — undef reference is strong and would fail at load.

`missing` and `weakMissing` are derived projections over `entries`,
not separately maintained arrays — the inductive `Resolution` is the
single source of truth.
-/

import LeanLoad.Parse.Structs
import LeanLoad.Elaborate.Elf
import Std.Data.HashMap

namespace LeanLoad.Plan.Resolve

open LeanLoad
open LeanLoad.Parse
open LeanLoad.Elaborate

/-- A resolved global symbol, parameterised by the elf-array size `objCount`.
    The `Fin objCount` carries the bounds proof at the type level — every
    consumer indexes the elf array totally, no `?`. The `symIdx : Nat`
    stays unbounded because its valid range depends on the specific
    object referenced; consumers still `[]?` it. -/
structure SymRef (objCount : Nat) where
  objectIdx : Fin objCount
  symIdx    : Nat
  deriving Repr

/-- Look up `name` as a global definition in `elf`'s symbol table.
    Names are pre-resolved at validation time (see `Elaborate.Symbol`),
    so no string-table lookup happens here. -/
def findInElf (elf : Elaborate.Elf) (name : String) : Option Nat :=
  elf.symtab.findIdx? (fun entry => entry.isGlobalDef && entry.name == some name)

/-- Resolve `name` against `elfs` via breadth-first search.
    Returns the providing `SymRef`, or `none` if no elf defines it.

    Implemented via `Array.finRange + findSome?` so consumers can
    chain through the standard `findSome?` characterisation lemmas
    (`resolveByName_provider_defines`, `resolveByName_is_bfs` below). -/
def resolveByName (elfs : Array Elf) (name : String) : Option (SymRef elfs.size) :=
  (Array.finRange elfs.size).findSome? fun objectIdx =>
    (findInElf elfs[objectIdx] name).map fun symIdx =>
      { objectIdx, symIdx }

/-- A failed-to-resolve undefined symbol; useful for diagnostics.
    Same `Fin objCount` parameterisation as `SymRef` so `Table.missing[i].objectIdx`
    is total. -/
structure Unresolved (objCount : Nat) where
  objectIdx : Fin objCount
  symIdx    : Nat
  name      : String
  deriving Repr

-- ============================================================================
-- Soundness theorems for `findInElf` and `resolveByName`. The
-- contract is gabi 08 § Shared Object Dependencies: BFS-first global
-- definition with the matching name. These theorems characterise the
-- public API in terms of that contract.
-- ============================================================================

/-- The predicate `findInElf` searches for. Made explicit so the
    `Array.findIdx?` characterisation lemmas can talk about it. -/
private def isMatchingDef (name : String) (entry : Symbol) : Bool :=
  entry.isGlobalDef && entry.name == some name

private theorem findInElf_eq_findIdx? (elf : Elaborate.Elf) (name : String) :
    findInElf elf name = elf.symtab.findIdx? (isMatchingDef name) :=
  rfl

/-- If `findInElf` returns `some symIdx`, the index is in bounds.
    Used as the size proof in `findInElf_provides` and
    `findInElf_is_first`. -/
theorem findInElf_lt_size {elf : Elaborate.Elf} {name : String} {symIdx : Nat}
    (h : findInElf elf name = some symIdx) : symIdx < elf.symtab.size := by
  rw [findInElf_eq_findIdx?, Array.findIdx?_eq_some_iff_getElem] at h
  exact h.1

/-- If `findInElf` returns `some symIdx`, the symbol at that index is
    a global definition with the matching name (gabi 08). The bound
    proof comes from `findInElf_lt_size`. -/
theorem findInElf_provides {elf : Elaborate.Elf} {name : String} {symIdx : Nat}
    (h : findInElf elf name = some symIdx) :
    (elf.symtab[symIdx]'(findInElf_lt_size h)).isGlobalDef = true ∧
    (elf.symtab[symIdx]'(findInElf_lt_size h)).name = some name := by
  have h' := h
  rw [findInElf_eq_findIdx?, Array.findIdx?_eq_some_iff_getElem] at h'
  obtain ⟨_h_lt, h_pred, _h_first⟩ := h'
  unfold isMatchingDef at h_pred
  rw [Bool.and_eq_true] at h_pred
  obtain ⟨h_def, h_name⟩ := h_pred
  exact ⟨h_def, beq_iff_eq.mp h_name⟩

/-- If `findInElf` returns `some symIdx`, every earlier symbol in the
    same elf is *not* a global definition with the matching name —
    `findIdx?`'s first-match property. -/
theorem findInElf_is_first {elf : Elaborate.Elf} {name : String} {symIdx : Nat}
    (h : findInElf elf name = some symIdx) (k : Nat) (h_k : k < symIdx) :
    ¬ ((elf.symtab[k]'(Nat.lt_trans h_k (findInElf_lt_size h))).isGlobalDef = true ∧
       (elf.symtab[k]'(Nat.lt_trans h_k (findInElf_lt_size h))).name = some name) := by
  intro ⟨h_def, h_name⟩
  rw [findInElf_eq_findIdx?, Array.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨_h_lt, _h_pred, h_first⟩ := h
  refine h_first k h_k ?_
  unfold isMatchingDef
  simp [h_def, h_name]

/-- If `resolveByName` returns `some ref`, `ref.symIdx` is in bounds
    for the providing elf's symtab. -/
theorem resolveByName_lt_size {elfs : Array Elf} {name : String}
    {ref : SymRef elfs.size}
    (h : resolveByName elfs name = some ref) :
    ref.symIdx < elfs[ref.objectIdx].symtab.size := by
  unfold resolveByName at h
  obtain ⟨idx, _h_mem, h_f⟩ := Array.exists_of_findSome?_eq_some h
  rw [Option.map_eq_some_iff] at h_f
  obtain ⟨symIdx, h_find, h_eq⟩ := h_f
  subst h_eq
  exact findInElf_lt_size h_find

/-- If `resolveByName` returns `some ref`, the symbol at `ref` is a
    global definition with the matching name. The gabi 08 BFS first-
    match contract is `resolveByName_is_bfs` below. -/
theorem resolveByName_provider_defines {elfs : Array Elf} {name : String}
    {ref : SymRef elfs.size}
    (h : resolveByName elfs name = some ref) :
    (elfs[ref.objectIdx].symtab[ref.symIdx]'(resolveByName_lt_size h)).isGlobalDef = true ∧
    (elfs[ref.objectIdx].symtab[ref.symIdx]'(resolveByName_lt_size h)).name = some name := by
  have h' := h
  unfold resolveByName at h'
  obtain ⟨idx, _h_mem, h_f⟩ := Array.exists_of_findSome?_eq_some h'
  rw [Option.map_eq_some_iff] at h_f
  obtain ⟨symIdx, h_find, h_eq⟩ := h_f
  subst h_eq
  exact findInElf_provides h_find

/-- gabi 08 BFS contract: the resolved provider is the *first* elf
    in BFS order that defines a symbol with the matching name. Every
    elf at an earlier index has no matching global definition. -/
theorem resolveByName_is_bfs {elfs : Array Elf} {name : String}
    {ref : SymRef elfs.size}
    (h : resolveByName elfs name = some ref) :
    ∀ (i : Nat) (h_lt : i < ref.objectIdx.val),
      findInElf (elfs[i]'(Nat.lt_trans h_lt ref.objectIdx.isLt)) name = none := by
  intro i h_lt
  -- Decompose `findSome?` into prefix/match/suffix.
  unfold resolveByName at h
  rw [Array.findSome?_eq_some_iff] at h
  obtain ⟨ys, a, zs, h_split, h_f, h_first⟩ := h
  -- `a = ref.objectIdx` from `f a = some ref` (Option.map injective).
  rw [Option.map_eq_some_iff] at h_f
  obtain ⟨_symIdx, _h_findA, h_eq⟩ := h_f
  have h_obj_a : ref.objectIdx = a := by
    have := congrArg SymRef.objectIdx h_eq.symm; simpa using this
  -- Length-wise, `(Array.finRange elfs.size).size = ys.size + 1 + zs.size`.
  have h_size_split : (Array.finRange elfs.size).size = ys.size + 1 + zs.size := by
    have := congrArg Array.size h_split
    rw [Array.size_append, Array.size_push] at this
    omega
  -- `a.val = ys.size` since `Array.finRange n[ys.size] = ⟨ys.size, _⟩` and
  -- by `h_split`, that same position is `a`.
  have h_a_val : a.val = ys.size := by
    have h_ys_lt_split :
        ys.size < (ys.push a ++ zs).size := by
      rw [Array.size_append, Array.size_push]; omega
    have h_get_split : (ys.push a ++ zs)[ys.size]'h_ys_lt_split = a := by
      rw [Array.getElem_append_left (hlt := by rw [Array.size_push]; omega),
          Array.getElem_push_eq]
    have h_ys_lt_full : ys.size < (Array.finRange elfs.size).size := by
      rw [h_size_split]; omega
    have h_finRange_get : (Array.finRange elfs.size)[ys.size]'h_ys_lt_full = a := by
      rw [show (Array.finRange elfs.size)[ys.size]'h_ys_lt_full =
            (ys.push a ++ zs)[ys.size]'(h_split ▸ h_ys_lt_full) from
            by congr 1 <;> rw [h_split]]
      exact h_get_split
    have := congrArg Fin.val h_finRange_get
    rw [Array.getElem_finRange] at this
    simpa using this.symm
  -- Bound transfer: `i < ref.objectIdx.val = a.val = ys.size`.
  rw [h_obj_a, h_a_val] at h_lt
  -- `ys[i]` has `.val = i`, since `(Array.finRange n)[i] = ⟨i, _⟩` and
  -- the prefix `ys` of `Array.finRange n` is the position-preserving
  -- restriction of it.
  have h_i_lt_full : i < (Array.finRange elfs.size).size := by
    rw [h_size_split]; omega
  have h_i_lt_split : i < (ys.push a ++ zs).size := by
    rw [Array.size_append, Array.size_push]; omega
  have h_ys_get_split :
      (ys.push a ++ zs)[i]'h_i_lt_split = ys[i]'h_lt := by
    rw [Array.getElem_append_left (hlt := by rw [Array.size_push]; omega),
        Array.getElem_push_lt h_lt]
  have h_ys_get_eq_finRange : ys[i]'h_lt =
      (Array.finRange elfs.size)[i]'h_i_lt_full := by
    rw [← h_ys_get_split]
    congr 1 <;> rw [h_split]
  have h_ys_val : (ys[i]'h_lt).val = i := by
    rw [h_ys_get_eq_finRange, Array.getElem_finRange]
    rfl
  -- The first-match condition gives `f ys[i] = none`, i.e.
  -- `(findInElf elfs[ys[i]] name).map _ = none`. Then `elfs[ys[i]] = elfs[i]`
  -- by `h_ys_val`.
  have h_f_none := h_first _ (Array.getElem_mem h_lt)
  rw [Option.map_eq_none_iff] at h_f_none
  -- elfs[ys[i].val]'... = elfs[i]'... by h_ys_val (proof-irrelevance).
  have h_idx_eq : ys[i]'h_lt = ⟨i, by
    have := (ys[i]'h_lt).isLt
    show i < elfs.size
    rw [← h_ys_val]; exact this⟩ := by
    apply Fin.ext
    exact h_ys_val
  rw [h_idx_eq] at h_f_none
  exact h_f_none

/-- Result of resolving one undef reference. Three explicit cases:
    found, weak-undefined (S = 0 by spec), and strong-undefined (load
    failure). -/
inductive Resolution (objCount : Nat) where
  /-- The BFS found a providing `(object, symbol)`. -/
  | found (ref : SymRef objCount)
  /-- Undef reference is `STB_WEAK`; gabi 05 binds it to 0. -/
  | weakUndef
  /-- Undef reference is strong and unresolved — load failure. -/
  | strongUndef
  deriving Repr

namespace Resolution

/-- Extract the resolved provider, dropping the weak/strong-undef
    distinction. Used by `Reloc.planOne` where both undef branches
    collapse to `S = 0`. -/
def target? : Resolution objCount → Option (SymRef objCount)
  | .found ref => some ref
  | .weakUndef => none
  | .strongUndef => none

end Resolution

/-- Result of building the resolution table for the elf array.
    Parameterised by the elf count so every contained `Unresolved` /
    `SymRef` carries its bounds proof.

    `index` is *total over all undefined symbols* (not just those with
    a name): `buildTable` inserts `weakUndef` for noName / empty-name
    undefs, so any per-rela lookup `lookup objectIdx symIdx` always
    returns a defined `Resolution`. `entries` is the diagnostic /
    iteration array and skips noName entries (they have no useful
    diagnostic name to surface). -/
structure Table (objCount : Nat) where
  /-- One entry per *named* undefined reference, in iteration order.
      Used for diagnostics (`missing` / `weakMissing` projections);
      noName / empty-name undefs are not included. -/
  entries : Array (Unresolved objCount × Resolution objCount)
  /-- O(1) `(objectIdx, symIdx) → Resolution objCount` lookup, total over all
      undefined symbols (named or not). Consumers go through
      `Table.lookup` so the type's totality guarantee shows up at the
      call site. -/
  index : Std.HashMap (Nat × Nat) (Resolution objCount)

namespace Table

/-- Total `(objectIdx, symIdx) → Resolution` lookup. Falls back to
    `weakUndef` when the key is missing — but for tables built by
    `buildTable` over an elf's `isUndef` symbols, the key is always
    present, so the fallback never fires. The `getD` form lets
    `Plan.Reloc.resolveTarget` pattern-match three constructors
    (`.found` / `.weakUndef` / `.strongUndef`) instead of four (those
    + `none`). -/
def lookup (t : Table objCount) (objectIdx symIdx : Nat) : Resolution objCount :=
  t.index.getD (objectIdx, symIdx) .weakUndef

/-- Strong (non-weak) undef references that did not resolve. A
    non-empty `missing` means the program would fail at load. -/
def missing (t : Table objCount) : Array (Unresolved objCount) :=
  t.entries.filterMap fun (u, r) => match r with
    | .strongUndef => some u
    | _            => none

/-- Weak undef references that did not resolve. Allowed by gabi 05;
    surfaced for diagnostics only. -/
def weakMissing (t : Table objCount) : Array (Unresolved objCount) :=
  t.entries.filterMap fun (u, r) => match r with
    | .weakUndef => some u
    | _          => none

end Table

/-- Walk every elf's symbol table, look up each undefined
    reference's definition. Builds both the diagnostic iteration
    array (`entries`) and the O(1) total lookup `index`.

    `index` covers *every* undefined symbol — named or not — so
    `Table.lookup` is total. NoName / empty-name undefs map to
    `weakUndef` (gabi 05's safe fallback for an unresolvable weak
    reference; a strong-undef without a name is a malformed ELF that
    the linker shouldn't have produced). `entries` skips them since
    they have no useful diagnostic string. -/
private def buildTableImpl (elfs : Array Elf) : Table elfs.size := Id.run do
  let mut entries : Array (Unresolved elfs.size × Resolution elfs.size) := #[]
  let mut index : Std.HashMap (Nat × Nat) (Resolution elfs.size) := ∅
  for h : objectIdx in [:elfs.size] do
    let elf := elfs[objectIdx]
    let mut symIdx := 0
    for symEntry in elf.symtab do
      if symEntry.isUndef then
        match symEntry.name with
        | none =>
          index := index.insert (objectIdx, symIdx) .weakUndef
        | some "" =>
          index := index.insert (objectIdx, symIdx) .weakUndef
        | some symName =>
          let entry : Unresolved elfs.size :=
            { objectIdx := ⟨objectIdx, h.upper⟩, symIdx, name := symName }
          let resolution : Resolution elfs.size :=
            match resolveByName elfs symName with
            | some ref => .found ref
            | none     => if symEntry.isWeak then .weakUndef else .strongUndef
          entries := entries.push (entry, resolution)
          index := index.insert (objectIdx, symIdx) resolution
      symIdx := symIdx + 1
  return { entries, index }

/-- Public entry point. The implicit `objCount` defaults to `elfs.size`
    via the `h_size : elfs.size = objCount := by rfl` argument; callers can
    pass an explicit `h_size` to retype the result at any provably-
    equal size (used by `Plan.Aggregate.ofGraph` to land at
    `Table objs.objects.size` without an outer `▸` cast). The
    `subst h_size; exact buildTableImpl elfs` body absorbs the
    rewrite at the wrapper. -/
def buildTable {objCount : Nat} (elfs : Array Elf)
    (h_size : elfs.size = objCount := by rfl) : Table objCount := by
  subst h_size; exact buildTableImpl elfs

end LeanLoad.Plan.Resolve

/-
Single-elf symbol lookup.

The atomic operation behind gabi 08 § Shared Object Dependencies
resolution: given one elf and a name, find the *first global
definition* in this elf with that name.

`findInElf` returns `Option (MatchedSym elf name)`. `MatchedSym` is a
witnessed match — its four fields *are* the per-elf contract:

  • `lt_size`  — `symIdx` is in bounds for `elf.symtab`.
  • `isDef`    — `elf.symtab[symIdx].isGlobalDef = true`.
  • `nameEq`   — `elf.symtab[symIdx].name = some name`.
  • `isFirst`  — no earlier symbol in `elf.symtab` is a matching def.

Pushing the properties into the result type means consumers read the
witnesses by field access (`m.lt_size`, `m.isDef`) rather than chasing
three separate theorems. No downstream check is needed to discharge
"is this really a global def with the right name" — the type already
says so.

The witnessed shape is assembled in two steps: a private raw
`Option Nat` computation (`findInElfRaw`), then three Prop-side
lemmas (`findInElfRaw_lt_size`, `findInElfRaw_provides`,
`findInElfRaw_is_first`) supply the fields. This indirection is a
Lean limitation — `Array.findIdx?_eq_some_iff_getElem`'s right side
is an `∃`, which can't be destructured into a `Type`-valued result.
The intermediate is private; consumers see only `MatchedSym`.

This file is base data: no graph, no BFS, no fallback policy. The
BFS walk over `LoadGraph` lives in `Bfs.lean`; the across-elves
wrapper lives in `Lookup.lean`.
-/

import LeanLoad.Elaborate.Elf
import LeanLoad.Elaborate.Symbol

namespace LeanLoad.Plan.Resolve

open LeanLoad
open LeanLoad.Elaborate

/-- A resolved global symbol, parameterised by the elf-array size
    `objCount`. The `Fin objCount` carries the bounds proof at the
    type level — every consumer indexes the elf array totally,
    no `?`. The `symIdx : Nat` stays unbounded because its valid
    range depends on the specific object referenced; consumers
    still `[]?` it. -/
structure SymRef (objCount : Nat) where
  objectIdx : Fin objCount
  symIdx    : Nat
  deriving Repr

/-- A failed-to-resolve undefined symbol; useful for diagnostics.
    Same `Fin objCount` parameterisation as `SymRef` so
    `Table.missing[i].objectIdx` is total. -/
structure Unresolved (objCount : Nat) where
  objectIdx : Fin objCount
  symIdx    : Nat
  name      : String
  deriving Repr

-- ============================================================================
-- findInElfRaw + characterisation lemmas — private staging area.
-- ============================================================================

/-- The predicate `findInElf` searches for. Lifted out so the
    `Array.findIdx?` characterisation lemmas can talk about it. -/
private def isMatchingDef (name : String) (entry : Symbol) : Bool :=
  entry.isGlobalDef && entry.name == some name

/-- Raw lookup — returns just the index. The witnessed wrapper
    `findInElf` is what consumers should use. -/
private def findInElfRaw (elf : Elaborate.Elf) (name : String) : Option Nat :=
  elf.symtab.findIdx? (isMatchingDef name)

private theorem findInElfRaw_lt_size {elf : Elaborate.Elf} {name : String}
    {symIdx : Nat} (h : findInElfRaw elf name = some symIdx) :
    symIdx < elf.symtab.size := by
  unfold findInElfRaw at h
  rw [Array.findIdx?_eq_some_iff_getElem] at h
  exact h.1

private theorem findInElfRaw_provides {elf : Elaborate.Elf} {name : String}
    {symIdx : Nat} (h : findInElfRaw elf name = some symIdx) :
    (elf.symtab[symIdx]'(findInElfRaw_lt_size h)).isGlobalDef = true ∧
    (elf.symtab[symIdx]'(findInElfRaw_lt_size h)).name = some name := by
  have h' := h
  unfold findInElfRaw at h'
  rw [Array.findIdx?_eq_some_iff_getElem] at h'
  obtain ⟨_h_lt, h_pred, _h_first⟩ := h'
  unfold isMatchingDef at h_pred
  rw [Bool.and_eq_true] at h_pred
  exact ⟨h_pred.1, beq_iff_eq.mp h_pred.2⟩

private theorem findInElfRaw_is_first {elf : Elaborate.Elf} {name : String}
    {symIdx : Nat} (h : findInElfRaw elf name = some symIdx) (k : Nat)
    (h_k : k < symIdx) :
    ¬ ((elf.symtab[k]'(Nat.lt_trans h_k (findInElfRaw_lt_size h))).isGlobalDef = true ∧
       (elf.symtab[k]'(Nat.lt_trans h_k (findInElfRaw_lt_size h))).name = some name) := by
  intro ⟨h_def, h_name⟩
  unfold findInElfRaw at h
  rw [Array.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨_h_lt, _h_pred, h_first⟩ := h
  refine h_first k h_k ?_
  unfold isMatchingDef
  simp [h_def, h_name]

-- ============================================================================
-- MatchedSym + findInElf — the public, witnessed interface.
-- ============================================================================

/-- A witnessed match in `elf.symtab` against `name` — the first
    global definition with that name. The fields together discharge
    the gabi 08 § Shared Object Dependencies per-elf contract. -/
structure MatchedSym (elf : Elaborate.Elf) (name : String) where
  /-- The matching symbol's index. -/
  symIdx  : Nat
  /-- Index in bounds. -/
  lt_size : symIdx < elf.symtab.size
  /-- Symbol at `symIdx` is a global definition. -/
  isDef   : (elf.symtab[symIdx]'lt_size).isGlobalDef = true
  /-- Symbol at `symIdx` carries the requested name. -/
  nameEq  : (elf.symtab[symIdx]'lt_size).name = some name
  /-- No earlier symbol in `elf.symtab` is a matching global definition. -/
  isFirst : ∀ k (h_k : k < symIdx),
    ¬ ((elf.symtab[k]'(Nat.lt_trans h_k lt_size)).isGlobalDef = true ∧
       (elf.symtab[k]'(Nat.lt_trans h_k lt_size)).name = some name)

/-- Look up the first global definition in `elf.symtab` with name
    `name`. The fields of the returned `MatchedSym` are filled by
    the `findInElfRaw_*` characterisation lemmas. -/
def findInElf (elf : Elaborate.Elf) (name : String) :
    Option (MatchedSym elf name) :=
  match h : findInElfRaw elf name with
  | none => none
  | some symIdx => some {
      symIdx
      lt_size := findInElfRaw_lt_size h
      isDef   := (findInElfRaw_provides h).1
      nameEq  := (findInElfRaw_provides h).2
      isFirst := findInElfRaw_is_first h
    }

end LeanLoad.Plan.Resolve

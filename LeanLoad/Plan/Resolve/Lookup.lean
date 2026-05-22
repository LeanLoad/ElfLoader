/-
Across-elves symbol lookup.

`resolveByName g order name` walks `order` (an array of elf indices
into `g.objects`) and runs `findInElf` on each elf in turn. Returns
the first match, wrapped as a `SymRef g.objects.size`.

Callers typically pass `order = bfsOrder g`, the BFS view from
`Bfs.lean`. Combined that way, the three soundness theorems below
discharge the gabi 08 § Shared Object Dependencies contract:

  • `resolveByName_lt_size`           — `ref.symIdx` is in bounds for
                                        the providing elf's symtab.
  • `resolveByName_provider_defines`  — the symbol at `ref` is a
                                        global definition with the
                                        matching name.
  • `resolveByName_is_bfs`            — first-match-along-`order`:
                                        no earlier elf in `order`
                                        defines a matching symbol.

The is_bfs theorem is stated abstractly over any `order` so it's a
pure consequence of `Array.findSome?`'s first-match property; the
BFS interpretation comes from `Bfs.bfsOrder` (combined with future
completeness work — see `Bfs.lean`'s deferred-theorems block).
-/

import LeanLoad.Plan.Resolve.Find
import LeanLoad.Discover.Graph

namespace LeanLoad.Plan.Resolve

open LeanLoad
open LeanLoad.Elaborate
open LeanLoad.Discover (LoadGraph)

/-- Resolve `name` against the loaded graph via traversal over
    `(g.objects, g.deps)` in `order` (typically `bfsOrder g`).
    Returns the providing `SymRef`, or `none` if no elf along
    `order` defines a matching global.

    Implemented via `Array.findSome?` so consumers can chain through
    the standard first-match characterisation lemmas below. -/
def resolveByName (g : LoadGraph) (order : Array (Fin g.objects.size))
    (name : String) : Option (SymRef g.objects.size) :=
  order.findSome? fun objectIdx =>
    (findInElf g.objects[objectIdx].elf name).map fun matched =>
      { objectIdx, symIdx := matched.symIdx }

-- ============================================================================
-- Soundness theorems — gabi 08 § Shared Object Dependencies BFS-first
-- contract.
-- ============================================================================

/-- If `resolveByName` returns `some ref`, `ref.symIdx` is in bounds
    for the providing elf's symtab. The bound comes straight off
    `MatchedSym.lt_size` of the underlying find. -/
theorem resolveByName_lt_size {g : LoadGraph}
    {order : Array (Fin g.objects.size)} {name : String}
    {ref : SymRef g.objects.size}
    (h : resolveByName g order name = some ref) :
    ref.symIdx < g.objects[ref.objectIdx].elf.symtab.size := by
  unfold resolveByName at h
  obtain ⟨_idx, _h_mem, h_f⟩ := Array.exists_of_findSome?_eq_some h
  rw [Option.map_eq_some_iff] at h_f
  obtain ⟨matched, _h_find, h_eq⟩ := h_f
  subst h_eq
  exact matched.lt_size

/-- If `resolveByName` returns `some ref`, the symbol at `ref` is a
    global definition with the matching name. Fields come straight
    off `MatchedSym.isDef` / `nameEq`. -/
theorem resolveByName_provider_defines {g : LoadGraph}
    {order : Array (Fin g.objects.size)} {name : String}
    {ref : SymRef g.objects.size}
    (h : resolveByName g order name = some ref) :
    (g.objects[ref.objectIdx].elf.symtab[ref.symIdx]'(resolveByName_lt_size h)).isGlobalDef = true ∧
    (g.objects[ref.objectIdx].elf.symtab[ref.symIdx]'(resolveByName_lt_size h)).name
        = some name := by
  have h' := h
  unfold resolveByName at h'
  obtain ⟨_idx, _h_mem, h_f⟩ := Array.exists_of_findSome?_eq_some h'
  rw [Option.map_eq_some_iff] at h_f
  obtain ⟨matched, _h_find, h_eq⟩ := h_f
  subst h_eq
  exact ⟨matched.isDef, matched.nameEq⟩

/-- First-match-along-`order` contract: the resolved provider is the
    first entry in `order` that defines a symbol with the matching
    name. Combined with `order = bfsOrder g`, this is the gabi 08
    § Shared Object Dependencies BFS-resolution contract.

    Stated abstractly over any `order` so it's a pure consequence of
    `Array.findSome?`'s first-match property. -/
theorem resolveByName_is_bfs {g : LoadGraph}
    {order : Array (Fin g.objects.size)} {name : String}
    {ref : SymRef g.objects.size}
    (h : resolveByName g order name = some ref) :
    ∃ (k : Nat) (h_k : k < order.size),
      order[k] = ref.objectIdx ∧
      ∀ (j : Nat) (h_j : j < k),
        findInElf
            (g.objects[order[j]'(Nat.lt_trans h_j h_k)]).elf
            name = none := by
  -- Decompose `findSome?` into prefix/match/suffix.
  unfold resolveByName at h
  rw [Array.findSome?_eq_some_iff] at h
  obtain ⟨ys, a, zs, h_split, h_f, h_first⟩ := h
  -- `a = ref.objectIdx` from `f a = some ref` (Option.map injective).
  rw [Option.map_eq_some_iff] at h_f
  obtain ⟨_matched, _h_findA, h_eq⟩ := h_f
  have h_obj_a : ref.objectIdx = a := by
    have := congrArg SymRef.objectIdx h_eq.symm; simpa using this
  -- The match position k = ys.size; bound from h_split.
  refine ⟨ys.size, ?_, ?_, ?_⟩
  · -- ys.size < order.size: from h_split, order = ys.push a ++ zs.
    have := congrArg Array.size h_split
    rw [Array.size_append, Array.size_push] at this
    omega
  · -- order[ys.size] = a = ref.objectIdx.
    have h_ys_lt_split : ys.size < (ys.push a ++ zs).size := by
      rw [Array.size_append, Array.size_push]; omega
    have h_get_split : (ys.push a ++ zs)[ys.size]'h_ys_lt_split = a := by
      rw [Array.getElem_append_left (hlt := by rw [Array.size_push]; omega),
          Array.getElem_push_eq]
    have h_order_get : order[ys.size]'(by
        rw [h_split, Array.size_append, Array.size_push]; omega) = a := by
      rw [show order[ys.size]'(by
            rw [h_split, Array.size_append, Array.size_push]; omega) =
          (ys.push a ++ zs)[ys.size]'h_ys_lt_split from by congr 1]
      exact h_get_split
    rw [h_obj_a]; exact h_order_get
  · -- For j < ys.size: order[j] is in ys (prefix), so f order[j] = none
    -- by h_first.
    intro j h_j
    have h_j_lt_split : j < (ys.push a ++ zs).size := by
      rw [Array.size_append, Array.size_push]; omega
    have h_ys_get_split : (ys.push a ++ zs)[j]'h_j_lt_split = ys[j]'h_j := by
      rw [Array.getElem_append_left (hlt := by rw [Array.size_push]; omega),
          Array.getElem_push_lt h_j]
    have h_order_get : order[j]'(by
        rw [h_split, Array.size_append, Array.size_push]; omega) = ys[j]'h_j := by
      rw [show order[j]'(by
            rw [h_split, Array.size_append, Array.size_push]; omega) =
          (ys.push a ++ zs)[j]'h_j_lt_split from by congr 1]
      exact h_ys_get_split
    have h_f_none := h_first _ (Array.getElem_mem h_j)
    rw [Option.map_eq_none_iff] at h_f_none
    -- `rw` would trip on the dependent proof of `order[j].val < objects.size`;
    -- rewrite the underlying Fin equality and let `simp` push it through.
    have h_objs_eq : g.objects[order[j]'(Nat.lt_trans h_j (by
        rw [h_split, Array.size_append, Array.size_push]; omega))]
        = g.objects[ys[j]'h_j] := by
      congr 1
    rw [h_objs_eq]
    exact h_f_none

end LeanLoad.Plan.Resolve

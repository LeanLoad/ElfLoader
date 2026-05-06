/-
Resolve-stage theorems (partial).

`findInObject` returning `some i` implies `i` is a valid index into
the providing object's `symtab`. Direct corollary of
`Array.findIdx?_eq_some_iff_findIdx_eq`.

The companion bound on `resolveByName`'s `objectIdx` requires
loop-invariant reasoning over the `for ... in g.objects do`
desugaring; left as future work.
-/

import LeanLoad.Resolve

namespace LeanLoad.Thm

open LeanLoad.Resolve

theorem findInObject_lt_size
    (obj : Discover.LoadedObject) (name : String) (i : Nat) :
    findInObject obj name = some i → i < obj.elf.symtab.size := by
  unfold findInObject
  intro h
  exact (Array.findIdx?_eq_some_iff_findIdx_eq.mp h).1

end LeanLoad.Thm

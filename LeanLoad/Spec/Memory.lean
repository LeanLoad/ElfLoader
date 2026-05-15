/-
Abstract byte-level memory state.

The pure half of the FFI axiom layer. `Memory` is a total function
`UInt64 → UInt8` — unmapped addresses return 0, which is the right
extensional answer because:

  · Our reservation is a single anonymous `mmap` block that the
    kernel zero-fills before any planned op runs (gabi 07 §
    Process Initialization; Linux `mmap(2)` MAP_ANONYMOUS).
  · Every planned op (`MmapOp` overlay, `ZeroOp` clear, `StoreOp`
    write) lands inside that block.
  · The three target soundness theorems (`bytes_preserved`,
    `bss_zeroed`, `relocs_applied`) only quantify over addresses
    inside the reservation, so the unmapped-equals-zero default
    never gets exercised.

Permissions are deliberately *not* modelled. All three soundness
theorems are byte equalities; access rights don't enter their
statements. If a later theorem demands them, add `perm : UInt64 →
Perm` as a parallel field and a corresponding `Op.applyPerm`.

Mirrors the IO interpreter shape in `Materialize/Safety.lean` —
each `MmapOp.apply` / `ZeroOp.apply` / `StoreOp.apply` /
`MprotectOp.apply` (in `Spec/Apply.lean`) is the pure denotation
of its `Op.run` partner.
-/

namespace LeanLoad.Spec

/-- Byte-level memory state. Total: every address has a defined byte.
    Initial state (`Memory.zero`) is all zeros, matching the kernel's
    `mmap(MAP_ANONYMOUS)` zero-fill guarantee for the reservation. -/
abbrev Memory : Type := UInt64 → UInt8

namespace Memory

/-- The all-zero memory state. Stands in for the post-`mmapAnon`
    state of the reservation. -/
def zero : Memory := fun _ => 0

@[simp] theorem zero_apply (a : UInt64) : (zero : Memory) a = 0 := rfl

end Memory

end LeanLoad.Spec

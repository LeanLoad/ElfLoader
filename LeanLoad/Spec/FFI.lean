/-
FFI axiom layer — the trust seam between Lean's IO and the
abstract memory model.

`LoadOps.runSafe` returns `IO Unit`. Its byte-level effect is
invisible to the pure layer because IO is sealed. To make the
effect reasonable about, we introduce a parameterised opaque
function `runSafe_image` that *names* the abstract memory state
the IO call leaves behind, and an axiom that pins down that
state to `LoadOps.apply`.

Trust surface — one opaque + one axiom:

  · `runSafe_image rsv lo safe fs : Memory` — opaque. Stands for
    "the byte-level memory at the moment `runSafe` returns
    control, restricted to the reservation". Opaque, not defined,
    because Lean's IO has no first-class memory denotation.

  · `runSafe_image_eq` — axiom. Says `runSafe_image` agrees with
    the pure denotation `LoadOps.apply fs lo Memory.zero`. This
    is the *only* claim about FFI behaviour — i.e., the only
    formal statement of "`runtime/runtime.c` actually implements
    the five extern primitives." A tier-4 kernel-level proof
    would discharge this axiom; today, audit by inspection.

Why a single end-to-end axiom rather than per-op axioms:

  · Smallest auditable surface — one item, not five.
  · No `StateT` refactor needed. `runSafe` stays in `IO Unit`.
  · The three soundness theorems we want
    (`bytes_preserved`, `bss_zeroed`, `relocs_applied`) are all
    statements about the *final* memory state — granular per-op
    reasoning is not required for them.
  · Per-op axioms are a conservative refinement: if a future
    theorem needs intermediate state, split this axiom into five
    without invalidating any existing proof that depended on it.

Scope of the axiom's "memory":

  Conceptually, `runSafe_image` is the loaded program's view of
  bytes in `[rsv.addr, rsv.addr + rsv.len)`. Outside that range,
  the host process's memory is whatever it was — the axiom makes
  no claim, and the pure denotation reads `0` (via `Memory.zero`)
  which need not match host reality. The soundness theorems
  quantify only over addresses inside the reservation, so this
  asymmetry does not affect any proof.

Living under `LeanLoad.Materialize.LoadOps` so the two new
declarations sit next to `LoadOps.runSafe` (in `Materialize/
Safety.lean`) — same namespace, same conceptual layer. A grep
for `axiom` outside `Runtime.lean` and `Spec/FFI.lean` should be
the only places to look for trust-surface items.
-/

import LeanLoad.Spec.Apply
import LeanLoad.Materialize.Safety

namespace LeanLoad.Materialize.LoadOps

open LeanLoad.Spec

-- ============================================================================
-- The opaque image of a successful `runSafe` call. Pinned down by the
-- axiom below.
-- ============================================================================

/-- The byte-level abstract memory state that `LoadOps.runSafe`
    leaves behind, parameterised by every input that determines its
    effect. Opaque — Lean's `IO Unit` has no first-class memory
    denotation, so we introduce one here and characterise it via
    `runSafe_image_eq`.

    Conceptually: the loaded program, the moment after `runSafe`
    returns and before the trampoline jumps, would observe these
    bytes when it reads any address inside `[rsv.addr, rsv.addr +
    rsv.len)`. -/
opaque runSafe_image
    {n : Nat} (rsv : Reserve)
    (lo : LoadOps n) (safe : LoadSafe rsv.addr rsv.len lo)
    (fs : File) : Memory

-- ============================================================================
-- The one axiom — the entire FFI trust statement for the materialize
-- seam.
-- ============================================================================

/-- The abstract memory state after a successful `runSafe` equals the
    pure denotation `LoadOps.apply` applied to `Memory.zero`. This is
    the single formal claim about the behaviour of `runtime/runtime.c`'s
    five extern primitives — discharging it requires a kernel-level
    semantic model (tier 4) and is currently audit-only.

    Consumers (soundness theorems) rewrite `runSafe_image …` through
    this equation, then reason structurally over `apply`. -/
axiom runSafe_image_eq
    {n : Nat} (rsv : Reserve)
    (lo : LoadOps n) (safe : LoadSafe rsv.addr rsv.len lo)
    (fs : File) :
    runSafe_image rsv lo safe fs = apply fs lo Memory.zero

end LeanLoad.Materialize.LoadOps

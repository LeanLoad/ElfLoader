/-
Trust seam: every `@[extern]` declaration that crosses into the C
shims under `runtime/`, the four typed slot records (`Mmap` / `Zero`
/ `Store` / `Mprotect`) that wrap each FFI signature, the per-slot
`run` dispatchers, and the `Disjoint` / `InRange` range predicates
the safety witness consumes.

`Materialize/LoadOps.lean` orchestrates the structured op tree
(`SegmentOps` / `ElfOps` / `LoadOps`) on top of these slot records
and exposes the witnessed entry point `LoadOps.runSafe`.

Reserve-then-overlay design:
  • At the IO boundary, `mmapAnon` requests a kernel-picked anon
    block large enough to hold every loaded object. The returned
    base is threaded into pure planning.
  • Structured slots in `LoadOps` only operate INSIDE that
    reservation. The reservation itself is not in the tree — it's a
    one-shot IO call before any planned slot runs.

The semantics of each extern match Linux `mmap(2)` / `mprotect(2)`.
Mappings live for the process lifetime; the kernel reclaims at exit.
Audited by inspection (~150 lines of C), not proven.
-/

namespace LeanLoad

namespace Runtime

-- ============================================================================
-- FileHandle — a transparent kernel fd. Held until process exit.
-- ============================================================================

abbrev FileHandle : Type := UInt32

@[extern "leanload_open"]
opaque openFile (path : @& String) : IO FileHandle

@[extern "leanload_pread"]
opaque pread (h : FileHandle) (offset : UInt64) (len : UInt64) : IO ByteArray

-- ============================================================================
-- FFI primitives — one Lean signature per C shim.
-- ============================================================================

/-- File-backed `MAP_PRIVATE | MAP_FIXED` mmap at `vaddr`.
    Replaces whatever was at `[vaddr, vaddr+len)` (intentionally — in
    our design that's the kernel-picked anon reservation). -/
@[extern "leanload_mmap_file"]
opaque mmapFile (h : FileHandle) (vaddr : UInt64) (len : UInt64)
    (prot : UInt32) (offset : UInt64) : IO Unit

/-- Kernel-picked anon mapping. `mmap(NULL, len, PROT_READ |
    PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, …)` — kernel returns
    the chosen base, guaranteed disjoint from any existing mapping
    in the host process. Used both for the per-load reservation
    (called once at the IO boundary before planning) and for the
    loaded program's stack (`MAP_STACK` on Linux is a no-op so we
    don't bother distinguishing). -/
@[extern "leanload_mmap_anon"]
opaque mmapAnon (len : UInt64) : IO UInt64

@[extern "leanload_mprotect"]
opaque mprotect (addr : UInt64) (len : UInt64) (prot : UInt32) : IO Unit

/-- Store the low 4 or 8 little-endian bytes of `value` at `addr`,
    selected by `size` (4 or 8). Used for relocation patches; the
    formula computes a `UInt64` and we truncate at memcpy time. -/
@[extern "leanload_store"]
opaque store (addr : UInt64) (size : UInt8) (value : UInt64) : IO Unit

/-- Zero `len` bytes starting at `addr`. Used for the partial-page
    BSS tail past `filesz` on a file mmap's last page (kernel maps
    file content there, not zero). -/
@[extern "leanload_zero"]
opaque zero (addr : UInt64) (len : UInt64) : IO Unit

-- ============================================================================
-- Control transfer (does not return).
-- ============================================================================

@[extern "leanload_exec_call_ctor"]
opaque callCtor (addr : UInt64) : IO Unit

@[extern "leanload_exec_run"]
opaque execAndJump
  (entry  : UInt64)
  (phdrVa : UInt64)
  (phent  : UInt64)
  (phnum  : UInt64)
  (baseVa : UInt64)
  (stackVa : UInt64)
  (stackLen : UInt64)
  (argv0  : @& String) : IO Unit

/-- POSIX `PROT_WRITE` — used to widen a file overlay's initial
    permission so relocation patches can write before the final
    `mprotect` drops the bit. -/
def PROT_WRITE : UInt32 := 2

end Runtime

-- ============================================================================
-- Typed slot records — each wraps the FFI signature of one of the
-- four kernel-state mutations we plan. `Materialize/LoadOps.lean`
-- assembles arrays of these into the per-segment tree.
-- ============================================================================

/-- File-backed `MAP_PRIVATE | MAP_FIXED` mmap. -/
structure Mmap where
  handle : Runtime.FileHandle
  addr   : UInt64
  len    : UInt64
  prot   : UInt32
  offset : UInt64

/-- Zero `len` bytes starting at `addr`. -/
structure Zero where
  addr : UInt64
  len  : UInt64

/-- Store the low `size` bytes (4 or 8) of `value` at `addr`. -/
structure Store where
  addr  : UInt64
  size  : UInt8
  value : UInt64

/-- Set protection on `[addr, addr+len)`. -/
structure Mprotect where
  addr : UInt64
  len  : UInt64
  prot : UInt32

/-- Width of a `Store` as a `UInt64`, for range arithmetic. -/
@[inline] def Store.byteLen (s : Store) : UInt64 := s.size.toUInt64

-- ============================================================================
-- Per-slot dispatchers — bridge a typed slot to its FFI primitive.
-- *Internal*: meant to be invoked only from
-- `Materialize.LoadOps.runSafe`, which has discharged the safety
-- witness. Direct use bypasses every safety check.
-- ============================================================================

namespace Mmap
def run (m : Mmap) : IO Unit :=
  Runtime.mmapFile m.handle m.addr m.len m.prot m.offset
end Mmap

namespace Zero
def run (z : Zero) : IO Unit :=
  Runtime.zero z.addr z.len
end Zero

namespace Store
def run (s : Store) : IO Unit :=
  Runtime.store s.addr s.size s.value
end Store

namespace Mprotect
def run (m : Mprotect) : IO Unit :=
  Runtime.mprotect m.addr m.len m.prot
end Mprotect

-- ============================================================================
-- Range arithmetic — predicates over `[addr, addr + len)` in `Nat`
-- to dodge UInt64 wrap. Consumed by the safety predicates in
-- `Materialize/LoadOps.lean`.
-- ============================================================================

namespace Runtime

/-- Two memory ranges don't overlap. -/
def Disjoint (a₁ l₁ a₂ l₂ : UInt64) : Prop :=
  a₁.toNat + l₁.toNat ≤ a₂.toNat ∨ a₂.toNat + l₂.toNat ≤ a₁.toNat

/-- An address range `[innerA, innerA+innerL)` is fully contained
    in `[outerA, outerA+outerL)`. -/
def InRange (innerA innerL outerA outerL : UInt64) : Prop :=
  outerA.toNat ≤ innerA.toNat ∧
  innerA.toNat + innerL.toNat ≤ outerA.toNat + outerL.toNat

instance (a₁ l₁ a₂ l₂ : UInt64) : Decidable (Disjoint a₁ l₁ a₂ l₂) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance (innerA innerL outerA outerL : UInt64) :
    Decidable (InRange innerA innerL outerA outerL) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Runtime

end LeanLoad

/-
Trust seam: every `@[extern]` declaration that crosses into the C
shims under `runtime/`, the five typed records (`Mmap` / `Zero` /
`Store` / `Mprotect` / `Reserve`) that wrap each FFI signature,
the per-record `run` dispatchers, and the `Disjoint` / `InRange`
range predicates the safety witness consumes.

The five kernel operations (`mmapFile`, `mprotect`, `store`, `zero`,
`mmapAnon`) are *private* externs — callers must go through the
typed records' `run` methods. That keeps the address-arithmetic
preconditions (the safety witnesses) in front of every FFI call.

`Materialize/LoadOps.lean` orchestrates the structured op tree
(`SegmentOps` / `ElfOps` / `LoadOps`) on top of these slot records
and exposes the witnessed entry point `LoadOps.runSafe`.

Reserve-then-overlay design:
  • At the IO boundary, `Reserve.run` requests a kernel-picked
    anon block large enough to hold every loaded object. The
    returned reservation carries the address + length + the no-wrap
    proof every safety predicate consumes.
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
-- FFI primitives — one Lean signature per C shim. *Private*: the
-- public path is via the typed slot records below (`Mmap.run` /
-- `Zero.run` / `Store.run` / `Mprotect.run` / `Reserve.run`).
-- ============================================================================

/-- File-backed `MAP_PRIVATE | MAP_FIXED` mmap at `vaddr`.
    Replaces whatever was at `[vaddr, vaddr+len)` (intentionally — in
    our design that's the kernel-picked anon reservation). -/
@[extern "leanload_mmap_file"]
private opaque mmapFile (h : FileHandle) (vaddr : UInt64) (len : UInt64)
    (prot : UInt32) (offset : UInt64) : IO Unit

/-- Kernel-picked anon mapping. `mmap(NULL, len, PROT_READ |
    PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, …)` — kernel returns
    the chosen base, guaranteed disjoint from any existing mapping
    in the host process. Callers go through `Reserve.run`,
    which wraps this with the no-wrap validation. -/
@[extern "leanload_mmap_anon"]
private opaque mmapAnon (len : UInt64) : IO UInt64

@[extern "leanload_mprotect"]
private opaque mprotect (addr : UInt64) (len : UInt64) (prot : UInt32) : IO Unit

/-- Store the low 4 or 8 little-endian bytes of `value` at `addr`,
    selected by `size` (4 or 8). Used for relocation patches; the
    formula computes a `UInt64` and we truncate at memcpy time. -/
@[extern "leanload_store"]
private opaque store (addr : UInt64) (size : UInt8) (value : UInt64) : IO Unit

/-- Zero `len` bytes starting at `addr`. Used for the partial-page
    BSS tail past `filesz` on a file mmap's last page (kernel maps
    file content there, not zero). -/
@[extern "leanload_zero"]
private opaque zero (addr : UInt64) (len : UInt64) : IO Unit

-- ============================================================================
-- Control transfer (does not return). Kept public — callers (Main)
-- need to invoke them after the LoadOps tree has been realized.
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
-- five kernel operations. `Materialize/LoadOps.lean` assembles the
-- four slot kinds into the per-segment tree; `Reserve` is the
-- one-shot anon allocation that bounds every slot.
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

/-- Anon reservation: address + length + the no-wrap proof every
    downstream safety predicate relies on. Used both for the per-load
    object reservation and for the loaded program's stack.

    A successful `mmap(MAP_ANONYMOUS)` on Linux always satisfies
    `addr + len < 2^64` (userspace VM is 48-bit), but the FFI layer
    can't prove that to Lean — so `Reserve.run` validates at
    runtime and converts the kernel's guarantee into a Lean proof. -/
structure Reserve where
  addr   : UInt64
  len    : UInt64
  noWrap : addr.toNat + len.toNat < 2 ^ 64

-- ============================================================================
-- Per-record `run` dispatchers — bridge a typed record to its FFI
-- primitive. The only path from Lean to the FFI: every external
-- call goes through one of these. The four slot `run`s execute
-- pre-planned data; `Reserve.run` requests a fresh allocation.
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

namespace Reserve
/-- Allocate a reservation of `len` bytes. Calls the private
    `Runtime.mmapAnon` extern and validates the no-wrap property at
    runtime. The validation is essentially free (one comparison) and
    the `.error` branch is unreachable on Linux (userspace addresses
    fit in 48 bits) — kept as a safety net so a non-Linux kernel
    returning a wrapping address fails loud. -/
def run (len : UInt64) : IO Reserve := do
  let addr ← Runtime.mmapAnon len
  if h : addr.toNat + len.toNat < 2 ^ 64 then
    return ⟨addr, len, h⟩
  else
    throw (IO.userError s!"Runtime.mmapAnon returned wrapping reservation \
      (addr=0x{addr.toNat}, len=0x{len.toNat})")
end Reserve

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

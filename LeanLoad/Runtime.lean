/-
Trust seam: every `@[extern]` declaration that crosses into the C
shims under `runtime/`, the five typed records (`MmapOp` / `ZeroOp` /
`StoreOp` / `MprotectOp` / `Reserve`) that wrap each FFI signature,
and the per-record `run` dispatchers.

The five kernel operations (`mmapFile`, `mprotect`, `store`, `zero`,
`mmapAnon`) are *private* externs — callers must go through the
typed records' `run` methods. That keeps the address-arithmetic
preconditions (the exec safety witnesses) in front of every FFI call.

`Exec/LoadOps.lean` orchestrates the structured load ops
(`SegmentOps` / `ElfOps` / `LoadOps`) on top of these op records
and exposes the witnessed entry point `LoadOps.runSafe`.

Reserve-then-overlay design:
  • At the IO boundary, `Reserve.run` requests a kernel-picked
    anon block large enough to hold every loaded object. The
    returned reservation carries the address + length + the no-wrap
    proof every safety predicate consumes.
  • Structured ops in `LoadOps` only operate INSIDE that
    reservation. The reservation itself is not in the tree — it's a
    one-shot IO call before any planned op runs.

The semantics of each extern match Linux `mmap(2)` / `mprotect(2)`.
Mappings live for the process lifetime; the kernel reclaims at exit.
Audited by inspection (~150 lines of C), not proven.
-/

namespace LeanLoad

namespace Runtime

-- ============================================================================
-- File — an open kernel fd plus the regular-file size observed at open time.
-- ============================================================================

/-- Open read-only file, held until process exit. `size` is captured with
    `fstat(2)` immediately after open so parse-time reads can reject ranges
    beyond EOF before calling `pread(2)`. -/
structure File where
  fd   : UInt32
  size : UInt64
  deriving Repr, Inhabited, BEq

namespace File

/-- Does `[off, off + len)` fit inside this file's observed byte size? -/
def containsRange (f : File) (off len : UInt64) : Prop :=
  off.toNat + len.toNat ≤ f.size.toNat

instance (f : File) (off len : UInt64) : Decidable (f.containsRange off len) := by
  unfold containsRange; infer_instance

end File

/-- Resolve a `DT_NEEDED` soname against `LD_LIBRARY_PATH` + the
    given `runpath`, open the resulting file `RDONLY | CLOEXEC`, and
    return the open file.

    Search rules (gabi 08 § Shared Object Dependencies):
      1. If `soname` contains '/', open as a literal path.
      2. Else search `LD_LIBRARY_PATH` (`:`-separated; first hit wins).
      3. Else search `runpath` (if `some`).
      4. Else `none`.

    Returns just the open file (no resolved path back) — the
    canonical dedup key is `DT_SONAME` with the requested name as
    fallback (see `Discover.DependencyFinder.io`), neither of which needs the
    resolved path. Implementation lives in `Runtime.c` — keeps the
    path splitting and `getenv` call out of Lean. -/
@[extern "leanload_open_by_name"]
private opaque openByNameFd (soname : @& String) (runpath : @& Option String) :
    IO (Option UInt32)

@[extern "leanload_file_size"]
private opaque fileSizeFd (fd : UInt32) : IO UInt64

/-- Resolve, open, and attach the observed file size. -/
def openByName (soname : String) (runpath : Option String) : IO (Option File) := do
  match ← openByNameFd soname runpath with
  | none    => pure none
  | some fd =>
      let size ← fileSizeFd fd
      pure (some { fd, size })

@[extern "leanload_pread"]
private opaque preadFd (fd : UInt32) (offset : UInt64) (len : UInt64) : IO ByteArray

/-- Bounded `pread(2)`: reject ranges outside the observed file size before
    crossing the FFI boundary. -/
def pread (f : File) (offset : UInt64) (len : UInt64) : IO ByteArray := do
  if _h : f.containsRange offset len then
    preadFd f.fd offset len
  else
    throw (IO.userError s!"pread out of bounds: offset 0x{offset.toNat}, \
      len {len.toNat}, file size {f.size.toNat}")

-- ============================================================================
-- FFI primitives — one Lean signature per C shim. *Private*: the
-- public path is via the typed op records below (`MmapOp.run` /
-- `Zero.run` / `Store.run` / `MprotectOp.run` / `Reserve.run`).
-- ============================================================================

/-- File-backed `MAP_PRIVATE | MAP_FIXED` mmap at `eaddr`.
    Replaces whatever was at `[eaddr, eaddr+len)` (intentionally — in
    our design that's the kernel-picked anon reservation). -/
@[extern "leanload_mmap_file"]
private opaque mmapFileFd (fd : UInt32) (eaddr : UInt64) (len : UInt64)
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
  (programHeaderVa : UInt64)
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
-- Typed op records — each wraps the FFI signature of one of the
-- five kernel operations. `Exec/LoadOps.lean` assembles the
-- four op kinds into the per-segment tree; `Reserve` is the
-- one-shot anon allocation that bounds every op.
-- ============================================================================

/-- File-backed `MAP_PRIVATE | MAP_FIXED` mmap. -/
structure MmapOp where
  handle : Runtime.File
  addr   : UInt64
  len    : UInt64
  prot   : UInt32
  offset : UInt64

/-- Zero `len` bytes starting at `addr`. -/
structure ZeroOp where
  addr : UInt64
  len  : UInt64

/-- Store the low `size` bytes (4 or 8) of `value` at `addr`. -/
structure StoreOp where
  addr  : UInt64
  size  : UInt8
  value : UInt64

/-- Set protection on `[addr, addr+len)`. -/
structure MprotectOp where
  addr : UInt64
  len  : UInt64
  prot : UInt32

/-- Width of a `StoreOp` as a `UInt64`, for range arithmetic. -/
@[inline] def StoreOp.byteLen (s : StoreOp) : UInt64 := s.size.toUInt64

/-- Anon reservation: address + length + the no-wrap proof every
    downstream safety predicate relies on. Used both for the per-layout
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
-- call goes through one of these. The four op `run`s execute
-- pre-planned data; `Reserve.run` requests a fresh allocation.
-- ============================================================================

namespace MmapOp
def run (m : MmapOp) : IO Unit :=
  Runtime.mmapFileFd m.handle.fd m.addr m.len m.prot m.offset
end MmapOp

namespace ZeroOp
def run (z : ZeroOp) : IO Unit :=
  Runtime.zero z.addr z.len
end ZeroOp

namespace StoreOp
def run (s : StoreOp) : IO Unit :=
  Runtime.store s.addr s.size s.value
end StoreOp

namespace MprotectOp
def run (m : MprotectOp) : IO Unit :=
  Runtime.mprotect m.addr m.len m.prot
end MprotectOp

namespace Reserve
/-- Allocate a reservation of exactly `len` bytes. Calls the private
    `Runtime.mmapAnon` extern and validates the no-wrap property at
    runtime. The returned subtype carries the proof `r.len = len`, so
    callers (e.g. `Exec.build`) can connect the reservation
    size to a `Layout`'s `totalSpan` without recourse to an IO-side
    coherence lemma.

    The validation is essentially free (one comparison) and the
    `.error` branch is unreachable on Linux (userspace addresses fit
    in 48 bits) — kept as a safety net so a non-Linux kernel
    returning a wrapping address fails loud. -/
def run (len : UInt64) : IO { r : Reserve // r.len = len } := do
  let addr ← Runtime.mmapAnon len
  if h : addr.toNat + len.toNat < 2 ^ 64 then
    return ⟨⟨addr, len, h⟩, rfl⟩
  else
    throw (IO.userError s!"Runtime.mmapAnon returned wrapping reservation \
      (addr=0x{addr.toNat}, len=0x{len.toNat})")
end Reserve

end LeanLoad

/-
Trust seam: every `@[extern]` declaration that crosses into the C
shims under `runtime/`, plus the `MemoryOp` abstraction over those
externs and the IO interpreter that dispatches each constructor.

Reserve-then-overlay design:
  • At the IO boundary, `mmapAnonAlloc` requests a kernel-picked
    anon block large enough to hold every loaded object. The
    returned base is threaded into pure planning.
  • The planned `Array MemoryOp` contains only ops that operate
    INSIDE that reservation: `mmapFile` overlays, `zeroout`,
    `mprotect`, and patches. The reservation itself is not in the
    op array — it's a one-shot IO call before any planned op runs.

Three layers:
  1. Externs (top half) — opaque `FileHandle`, mmap variants,
     mprotect, raw writes, ctor calls, exec/jump.
  2. `MemoryOp` — pure data type for fire-and-forget kernel calls.
  3. `runSafe` — IO interpreter; only path to the kernel from
     planned ops.

The semantics of each extern match Linux `mmap(2)` / `mprotect(2)`.
Mappings live for the process lifetime; the kernel reclaims at exit.
Audited by inspection (~150 lines of C), not proven.
-/

namespace LeanLoad

namespace Runtime

-- ============================================================================
-- FileHandle — a transparent kernel fd. Held until process exit.
-- ============================================================================

def FileHandle : Type := UInt32
instance : Inhabited FileHandle := inferInstanceAs (Inhabited UInt32)

@[extern "leanload_open"]
opaque openFile (path : @& String) : IO FileHandle

@[extern "leanload_pread"]
opaque pread (h : FileHandle) (offset : UInt64) (len : UInt64) : IO ByteArray

/-- File-backed `MAP_PRIVATE | MAP_FIXED` overlay at `vaddr`. Used
    by `MemoryOp.mmapFile` for per-segment file content. Replaces
    whatever was at `[vaddr, vaddr+len)` (intentionally — in our
    design that's the kernel-picked anon reservation). -/
@[extern "leanload_mmap_file"]
opaque mmap (h : FileHandle) (vaddr : UInt64) (len : UInt64)
    (prot : UInt32) (offset : UInt64) : IO Unit

/-- Kernel-picked anon reservation. `mmap(NULL, len, PROT_READ |
    PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, …)` — kernel returns
    the chosen base, guaranteed disjoint from any existing mapping
    in the host process. Called once at the IO boundary before any
    planned op runs. -/
@[extern "leanload_mmap_alloc"]
opaque mmapAnonAlloc (len : UInt64) : IO UInt64

/-- Anonymous `MAP_STACK` mapping for the loaded program's stack;
    kernel chooses the address. -/
@[extern "leanload_mmap_stack"]
opaque mmapStack (len : UInt64) : IO UInt64

@[extern "leanload_mprotect"]
opaque mprotect (addr : UInt64) (len : UInt64) (prot : UInt32) : IO Unit

/-- Write the low 4 or 8 little-endian bytes of `value` at `addr`,
    selected by `size` (4 or 8). Used for relocation patches; the
    formula computes a `UInt64` and we truncate at memcpy time. -/
@[extern "leanload_write"]
opaque write (addr : UInt64) (size : UInt8) (value : UInt64) : IO Unit

/-- Zero `len` bytes starting at `addr`. Used for the partial-page
    BSS tail past `filesz` on a file overlay's last page (kernel
    maps file content there, not zero). -/
@[extern "leanload_zeroout"]
opaque zeroout (addr : UInt64) (len : UInt64) : IO Unit

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
-- MemoryOp — fire-and-forget kernel-state mutations that run INSIDE
-- the kernel-picked anon reservation. No `mmapAnon` constructor:
-- the reservation is a one-shot IO call (`mmapAnonAlloc`) at the IO
-- boundary, not part of the planned op array.
-- ============================================================================

/-- One *kernel-state mutation* the loader asks for inside the
    reservation. -/
inductive MemoryOp where
  /-- File-backed `MAP_PRIVATE | MAP_FIXED` overlay. Replaces the
      anon backing for `[addr, addr+len)` with file bytes. -/
  | mmapFile (handle : Runtime.FileHandle) (addr len : UInt64)
             (prot : UInt32) (offset : UInt64)
  /-- Zero `len` bytes at `addr`. -/
  | zeroout (addr len : UInt64)
  /-- Set protection on `[addr, addr+len)`. -/
  | mprotect (addr len : UInt64) (prot : UInt32)
  /-- Write the low `size` bytes (4 or 8) of `value` at `addr`. -/
  | write (addr : UInt64) (size : UInt8) (value : UInt64)

namespace MemoryOp

/-- Interpret an op list in order. **Private**: the only public entry
    point is `runSafe`, which requires the safety witness. -/
private def runAllUnsafe (ops : Array MemoryOp) : IO Unit := ops.forM fun op =>
  match op with
  | .mmapFile h addr len prot offset => Runtime.mmap h addr len prot offset
  | .zeroout  addr len               => Runtime.zeroout addr len
  | .mprotect addr len prot          => Runtime.mprotect addr len prot
  | .write    addr size value        => Runtime.write addr size value

-- ============================================================================
-- Per-op accessors and kind predicates.
-- ============================================================================

/-- The op's target address. -/
def addr : MemoryOp → UInt64
  | .mmapFile _ a _ _ _ => a
  | .zeroout  a _       => a
  | .mprotect a _ _     => a
  | .write    a _ _     => a

/-- The op's memory-range length. -/
def len : MemoryOp → UInt64
  | .mmapFile _ _ l _ _ => l
  | .zeroout  _ l       => l
  | .mprotect _ l _     => l
  | .write    _ s _     => s.toUInt64

/-- The op overlays a file inside the reservation. -/
def IsOverlay : MemoryOp → Prop
  | .mmapFile .. => True
  | _            => False

instance (op : MemoryOp) : Decidable op.IsOverlay := by
  cases op <;> simp [IsOverlay] <;> infer_instance

/-- The op writes bytes (zeroout + relocation writes). -/
def IsWrite : MemoryOp → Prop
  | .zeroout .. => True
  | .write   .. => True
  | _           => False

instance (op : MemoryOp) : Decidable op.IsWrite := by
  cases op <;> simp [IsWrite] <;> infer_instance

/-- The op changes page protection. -/
def IsMprotect : MemoryOp → Prop
  | .mprotect .. => True
  | _            => False

instance (op : MemoryOp) : Decidable op.IsMprotect := by
  cases op <;> simp [IsMprotect] <;> infer_instance

-- ============================================================================
-- Range arithmetic — predicates over `[addr, addr + len)` in `Nat`
-- to dodge UInt64 wrap.
-- ============================================================================

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

end MemoryOp

-- ============================================================================
-- Top-level safety predicates, parameterized by the reservation range
-- `[rsvAddr, rsvAddr + rsvLen)` returned by `Runtime.mmapAnonAlloc`.
-- Together they assert: file overlays don't collide with each other,
-- and every overlay / write / mprotect lies inside the reservation.
-- ============================================================================

/-- File overlays are pairwise disjoint. -/
def OverlaysDisjoint (ops : Array MemoryOp) : Prop :=
  ∀ i, ∀ _ : i < ops.size, ∀ j, ∀ _ : j < ops.size, i < j →
    ops[i].IsOverlay → ops[j].IsOverlay →
    MemoryOp.Disjoint ops[i].addr ops[i].len ops[j].addr ops[j].len

/-- Every overlay lies inside the reservation. -/
def OverlaysContained (rsvAddr rsvLen : UInt64) (ops : Array MemoryOp) : Prop :=
  ∀ i, ∀ _ : i < ops.size, ops[i].IsOverlay →
    MemoryOp.InRange ops[i].addr ops[i].len rsvAddr rsvLen

/-- Every write op lies inside the reservation. -/
def WritesContained (rsvAddr rsvLen : UInt64) (ops : Array MemoryOp) : Prop :=
  ∀ i, ∀ _ : i < ops.size, ops[i].IsWrite →
    MemoryOp.InRange ops[i].addr ops[i].len rsvAddr rsvLen

/-- Every mprotect op lies inside the reservation. -/
def MprotectsContained (rsvAddr rsvLen : UInt64) (ops : Array MemoryOp) : Prop :=
  ∀ i, ∀ _ : i < ops.size, ops[i].IsMprotect →
    MemoryOp.InRange ops[i].addr ops[i].len rsvAddr rsvLen

instance (ops : Array MemoryOp) : Decidable (OverlaysDisjoint ops) := by
  unfold OverlaysDisjoint; infer_instance

instance (rsvAddr rsvLen : UInt64) (ops : Array MemoryOp) :
    Decidable (OverlaysContained rsvAddr rsvLen ops) := by
  unfold OverlaysContained; infer_instance

instance (rsvAddr rsvLen : UInt64) (ops : Array MemoryOp) :
    Decidable (WritesContained rsvAddr rsvLen ops) := by
  unfold WritesContained; infer_instance

instance (rsvAddr rsvLen : UInt64) (ops : Array MemoryOp) :
    Decidable (MprotectsContained rsvAddr rsvLen ops) := by
  unfold MprotectsContained; infer_instance

namespace MemoryOp

/-- Interpret a safety-witnessed op list, given the reservation
    range that bounds every op. The witness fields are erased; the
    IO behaviour is identical to a plain `forM` over the array. -/
def runSafe (rsvAddr rsvLen : UInt64)
    (ops : { ops : Array MemoryOp //
      OverlaysDisjoint ops ∧
      OverlaysContained rsvAddr rsvLen ops ∧
      WritesContained rsvAddr rsvLen ops ∧
      MprotectsContained rsvAddr rsvLen ops }) :
    IO Unit := runAllUnsafe ops.val

end MemoryOp

end LeanLoad

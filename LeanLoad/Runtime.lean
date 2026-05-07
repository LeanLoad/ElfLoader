/-
The trust seam: every `@[extern]` declaration that crosses into the
C shims under `runtime/`. A grep for `@[extern]` outside this file
is a smell.

Two topic groups:
  1. Memory regions (`runtime/region.c`) — opaque mmap'd handles
     plus the operations the planner emits (mmap variants,
     mprotect, write, base-address read).
  2. Control transfer (`runtime/exec.c`) — calling individual
     constructors and the does-not-return jump that hands control
     to the loaded image.

The C side picks the `MAP_*` flag set per usage pattern (anonymous,
fixed, stack), so Lean callers don't reason about flag bitmasks.
`PROT_*` bits *do* cross the boundary because the planner reasons
per-segment about R/W/X (gabi 07 § Segment Permissions).

The semantics of each operation match Linux `mmap(2)` /
`mprotect(2)`. Mappings live for the process lifetime; the kernel
reclaims at exit. Audited by inspection (~150 lines of C), not
proven.

# Capability layer (`Ops`)

The actual loader pipeline does not call externs directly. Instead
it threads a `Runtime.Ops` capability record that bundles every IO
operation the loader can perform. Two implementations are provided:

  - `Ops.real` — calls the externs above. Used by `Main.load`/`debug`.
  - `Ops.inMemory` — pure-Lean simulation backed by `ByteArray` for
    files and `IO.Ref ByteArray` for mmap regions. Used by tests
    that want to drive the loader without a real kernel.

Pure planners (`DiscoverPlan`, `Layout`, `MapPlan`, `RelocPlan`,
`InitPlan`) never touch `Ops`. Only the IO appliers do.
-/

import Std.Data.HashMap

namespace LeanLoad.Runtime

-- ============================================================================
-- Real backends — C-allocated handles, identical to the previous
-- opaque `FileHandle` / `Region` types but renamed so the public
-- types below can wrap either real or mock variants.
-- ============================================================================

private opaque RealFileHandlePointed : NonemptyType
def RealFileHandle : Type := RealFileHandlePointed.type
instance : Nonempty RealFileHandle := RealFileHandlePointed.property

private opaque RealRegionPointed : NonemptyType
def RealRegion : Type := RealRegionPointed.type
instance : Nonempty RealRegion := RealRegionPointed.property

@[extern "leanload_filehandle_open"]
private opaque realOpen (path : @& String) : IO RealFileHandle
@[extern "leanload_filehandle_pread"]
private opaque realPread (h : @& RealFileHandle) (offset : UInt64) (len : UInt64) : IO ByteArray
@[extern "leanload_filehandle_mmap"]
private opaque realMmap (h : @& RealFileHandle) (vaddr : UInt64) (len : UInt64)
    (prot : UInt32) (offset : UInt64) : IO RealRegion

@[extern "leanload_region_mmap_reserve"]
private opaque realMmapReserve (vaddr : UInt64) (len : UInt64) : IO RealRegion
@[extern "leanload_region_mmap_stack"]
private opaque realMmapStack (len : UInt64) : IO RealRegion

@[extern "leanload_region_mprotect"]
private opaque realMprotect (r : @& RealRegion) (offset length : UInt64)
    (prot : UInt32) : IO Unit
@[extern "leanload_region_patch64"]
private opaque realPatch64 (region : @& RealRegion) (offset : UInt64) (value : UInt64) : IO Unit
@[extern "leanload_region_patch32"]
private opaque realPatch32 (region : @& RealRegion) (offset : UInt64) (value : UInt64) : IO Unit
@[extern "leanload_region_zeroout"]
private opaque realZeroout (region : @& RealRegion) (offset len : UInt64) : IO Unit

@[extern "leanload_exec_run"]
private opaque realExecAndJump
  (entry  : UInt64)
  (phdrVa : UInt64)
  (phent  : UInt64)
  (phnum  : UInt64)
  (baseVa : UInt64)
  (stack  : @& RealRegion)
  (argv0  : @& String) : IO Unit
@[extern "leanload_exec_call_ctor"]
private opaque realCallCtor (addr : UInt64) : IO Unit

-- ============================================================================
-- Public types: real-or-mock sum.
-- `LoadedObject.handle`, `ObjectImage.{reservation,segments}` etc.
-- store these — same name as before, sum type now.
-- ============================================================================

/-- Read-only file handle. Either a real kernel fd (`open(2)`-backed)
    or an in-memory `ByteArray` for tests. Read paths (`pread`)
    dispatch on the variant; the loader never constructs handles
    directly, it always goes through `Ops.open`. -/
inductive FileHandle where
  | real (h : RealFileHandle)
  | mock (path : String) (bytes : ByteArray)

/-- mmap'd memory region indexed by its byte length at the type
    level. The size parameter is a *ghost* value — the C side
    `leanload_region` already stores its own length, and the Lean
    type just refines that to enable type-level bounds checks at
    `patch{32,64}` / `mprotect` / `zeroout`. Constructors
    (`Ops.mmap{,Reserve,Stack}`) thread the requested length into
    the index so callers see the size as a static property.

    Either a real kernel mapping or an in-memory mutable byte buffer
    for tests. Mock regions carry a `vaddr` for diagnostics and a
    mutable `IO.Ref ByteArray` so writes can update in place. -/
inductive Region (size : UInt64) where
  | real (r : RealRegion)
  | mock (vaddr : UInt64) (bytes : IO.Ref ByteArray)

/-- Bounds predicate for write/protect operations on a `Region size`.
    Uses UInt64 comparisons (saturating subtraction) to sidestep
    UInt64 overflow concerns — `length ≤ size - offset` is
    well-defined regardless of arithmetic wrap. -/
def Region.InRange (size offset length : UInt64) : Prop :=
  offset ≤ size ∧ length ≤ size - offset

instance (size offset length : UInt64) : Decidable (Region.InRange size offset length) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `PROT_WRITE` bit, used by Map to widen a file-backed segment's
    initial protection so partial-last-page BSS can be zeroed before
    `mprotect` drops the bit for read-only segments. The
    planner-side `Layout.protOfFlags` produces the *final* per-segment
    `PROT_*` value (PF_R/W/X mapped to PROT_READ/WRITE/EXEC). -/
def PROT_WRITE : UInt32 := 2

-- ============================================================================
-- Capability record: every IO operation the loader can perform.
-- ============================================================================

/-- Bundle of IO operations the loader needs from "the world". A
    `Runtime.Ops` value is passed through every `*Apply` stage; pure
    planners don't see it. Two implementations: `real` (kernel) and
    `inMemory` (simulated, for tests). -/
structure Ops where
  «open»        : String → IO FileHandle
  pread         : FileHandle → UInt64 → UInt64 → IO ByteArray
  /-- File-backed `MAP_PRIVATE | MAP_FIXED` overlay; size index of
      the returned `Region` matches the `len` argument. -/
  mmap          : FileHandle → UInt64 → (len : UInt64) → UInt32 → UInt64 → IO (Region len)
  /-- Anonymous `MAP_FIXED` reservation; size index matches `len`. -/
  mmapReserve   : UInt64 → (len : UInt64) → IO (Region len)
  /-- Anonymous `MAP_STACK`; size index matches `len`. -/
  mmapStack     : (len : UInt64) → IO (Region len)
  /-- `mprotect` a sub-range. The bound proof `Region.InRange size
      offset length` discharges the kernel-level OOB check at the
      type level — no C-side bounds check needed. -/
  mprotect      : ∀ {size : UInt64}, Region size → (offset length : UInt64) →
                  (h : Region.InRange size offset length) → UInt32 → IO Unit
  patch64       : ∀ {size : UInt64}, Region size → (offset : UInt64) →
                  (h : Region.InRange size offset 8) → UInt64 → IO Unit
  patch32       : ∀ {size : UInt64}, Region size → (offset : UInt64) →
                  (h : Region.InRange size offset 4) → UInt64 → IO Unit
  zeroout       : ∀ {size : UInt64}, Region size → (offset length : UInt64) →
                  (h : Region.InRange size offset length) → IO Unit
  execAndJump   : ∀ {size : UInt64}, UInt64 → UInt64 → UInt64 → UInt64 → UInt64 →
                  Region size → String → IO Unit
  callCtor      : UInt64 → IO Unit

-- ============================================================================
-- Real implementation — dispatches mock variants where it can read
-- from them (e.g. `pread` of a mock file is a `ByteArray.extract`)
-- and errors where it can't (mock regions can't be `mmap`'d into a
-- real address space).
-- ============================================================================

private def realOpenOp : String → IO FileHandle :=
  fun p => .real <$> realOpen p

private def realPreadOp : FileHandle → UInt64 → UInt64 → IO ByteArray
  | .real h, off, len => realPread h off len
  | .mock _ b, off, len =>
    pure (b.extract off.toNat (off.toNat + len.toNat))

private def realMmapOp :
    FileHandle → UInt64 → (len : UInt64) → UInt32 → UInt64 → IO (Region len)
  | .real h, va, len, prot, off => .real <$> realMmap h va len prot off
  | .mock _ _, _, _, _, _ =>
    throw (IO.userError "Ops.real.mmap: mock files cannot be mapped into real memory")

private def realMmapReserveOp (va : UInt64) (len : UInt64) : IO (Region len) :=
  .real <$> realMmapReserve va len

private def realMmapStackOp (len : UInt64) : IO (Region len) :=
  .real <$> realMmapStack len

private def realMprotectOp {size : UInt64} :
    Region size → (offset length : UInt64) → Region.InRange size offset length →
    UInt32 → IO Unit
  | .real r, off, len, _h, prot => realMprotect r off len prot
  | .mock _ _, _, _, _, _ => pure ()  -- mock has no protection bits to toggle

private def mockWriteLE (ref : IO.Ref ByteArray) (off : UInt64) (width : Nat)
    (v : UInt64) : IO Unit := do
  let mut b ← ref.get
  for i in [:width] do
    b := b.set! (off.toNat + i) ((v >>> (i * 8).toUInt64).toUInt8)
  ref.set b

private def mockZeroout (ref : IO.Ref ByteArray) (off len : UInt64) : IO Unit := do
  let mut b ← ref.get
  for i in [:len.toNat] do
    b := b.set! (off.toNat + i) 0
  ref.set b

private def realPatch64Op {size : UInt64} :
    Region size → (offset : UInt64) → Region.InRange size offset 8 → UInt64 → IO Unit
  | .real r, off, _h, v => realPatch64 r off v
  | .mock _ ref, off, _h, v => mockWriteLE ref off 8 v

private def realPatch32Op {size : UInt64} :
    Region size → (offset : UInt64) → Region.InRange size offset 4 → UInt64 → IO Unit
  | .real r, off, _h, v => realPatch32 r off v
  | .mock _ ref, off, _h, v => mockWriteLE ref off 4 v

private def realZerooutOp {size : UInt64} :
    Region size → (offset length : UInt64) → Region.InRange size offset length → IO Unit
  | .real r, off, len, _h => realZeroout r off len
  | .mock _ ref, off, len, _h => mockZeroout ref off len

private def realExecAndJumpOp {size : UInt64}
    (entry phdrVa phent phnum baseVa : UInt64) (stack : Region size) (argv0 : String) :
    IO Unit :=
  match stack with
  | .real r => realExecAndJump entry phdrVa phent phnum baseVa r argv0
  | .mock _ _ =>
    throw (IO.userError "Ops.real.execAndJump: cannot transfer control to a mock stack")

/-- Real (kernel-backed) implementation of `Ops`. Used by `Main.load`
    and `Main.debug`. Mock variants of `FileHandle`/`Region` are
    handled where it makes sense (read mock file, write mock region)
    and rejected where it doesn't (mmap'ing a mock file, jumping to
    a mock stack). -/
def Ops.real : Ops :=
  { «open»        := realOpenOp
    pread         := realPreadOp
    mmap        := realMmapOp
    mmapReserve := realMmapReserveOp
    mmapStack     := realMmapStackOp
    mprotect := realMprotectOp
    patch64       := realPatch64Op
    patch32       := realPatch32Op
    zeroout       := realZerooutOp
    execAndJump   := realExecAndJumpOp
    callCtor      := realCallCtor }

-- ============================================================================
-- In-memory implementation — pure-Lean simulation. Used by tests
-- that want to drive the loader through Parse → Discover → Layout →
-- Map → Reloc → Apply without ever entering the kernel.
-- ============================================================================

/-- Record of a captured `execAndJump` invocation. Mock cannot
    actually transfer control, so it stores the inputs for tests to
    inspect. -/
structure ExecRecord where
  entry  : UInt64
  phdrVa : UInt64
  phent  : UInt64
  phnum  : UInt64
  baseVa : UInt64
  /-- Stack region's `vaddr` (mock stacks have a fake vaddr; tests
      rarely care, the values populated *into* the stack are what
      matter and live in the captured stack region itself). -/
  stack  : UInt64
  argv0  : String
  deriving Repr

/-- Record of a captured `callCtor` invocation. -/
abbrev CtorRecord := UInt64

private def inMemoryOpenOp (files : Std.HashMap String ByteArray) :
    String → IO FileHandle :=
  fun p =>
    match files[p]? with
    | some b => pure (.mock p b)
    | none   => throw (IO.userError s!"inMemory.open: no such file '{p}'")

private def inMemoryPreadOp : FileHandle → UInt64 → UInt64 → IO ByteArray
  | .mock _ b, off, len =>
    pure (b.extract off.toNat (off.toNat + len.toNat))
  | .real _, _, _ =>
    throw (IO.userError "inMemory.pread: real handle leaked into mock loader")

/-- File-backed mmap in the mock world: copy the file slice into a
    fresh mutable buffer at `vaddr`. Page-alignment matters for the
    real kernel; the mock just keeps the bytes. -/
private def inMemoryMmapOp :
    FileHandle → UInt64 → (len : UInt64) → UInt32 → UInt64 → IO (Region len)
  | .mock _ b, va, len, _prot, off => do
    let slice := b.extract off.toNat (off.toNat + len.toNat)
    let ref ← IO.mkRef slice
    pure (.mock va ref)
  | .real _, _, _, _, _ =>
    throw (IO.userError "inMemory.mmap: real handle leaked")

private def inMemoryMmapReserveOp (va : UInt64) (len : UInt64) : IO (Region len) := do
  let ref ← IO.mkRef (ByteArray.mk (Array.replicate len.toNat 0))
  pure (.mock va ref)

private def inMemoryMmapStackOp (len : UInt64) : IO (Region len) := do
  let ref ← IO.mkRef (ByteArray.mk (Array.replicate len.toNat 0))
  pure (.mock 0 ref)

/-- Build an in-memory `Ops` whose `open` reads from `files` (a
    soname/path → bytes map) and whose mmap regions are mutable
    `IO.Ref ByteArray`s. `execAndJump` and `callCtor` capture their
    arguments into the supplied `IO.Ref`s for tests to inspect.

    Limitations: cannot run constructor or entry code (would need a
    JIT — out of scope); `mprotect` is a no-op since mock regions
    have no protection bits.

    Pass `execLog := none` if you don't care about the captured exec
    record (e.g. tests that stop before Exec). -/
def Ops.inMemory
    (files    : Std.HashMap String ByteArray)
    (execLog  : Option (IO.Ref (Array ExecRecord)) := none)
    (ctorLog  : Option (IO.Ref (Array CtorRecord)) := none) : Ops :=
  let execOp : ∀ {size : UInt64}, UInt64 → UInt64 → UInt64 → UInt64 → UInt64 →
               Region size → String → IO Unit :=
    fun entry phdrVa phent phnum baseVa stack argv0 => do
      let stackVa := match stack with | .mock va _ => va | .real _ => 0
      match execLog with
      | some ref =>
        ref.modify (·.push { entry, phdrVa, phent, phnum, baseVa, stack := stackVa, argv0 })
      | none => pure ()
  let ctorOp : UInt64 → IO Unit := fun addr => do
    match ctorLog with
    | some ref => ref.modify (·.push addr)
    | none     => pure ()
  { «open»        := inMemoryOpenOp files
    pread         := inMemoryPreadOp
    mmap          := inMemoryMmapOp
    mmapReserve   := inMemoryMmapReserveOp
    mmapStack     := inMemoryMmapStackOp
    mprotect      := fun _ _ _ _ _ => pure ()
    patch64       := realPatch64Op
    patch32       := realPatch32Op
    zeroout       := realZerooutOp
    execAndJump   := execOp
    callCtor      := ctorOp }

end LeanLoad.Runtime

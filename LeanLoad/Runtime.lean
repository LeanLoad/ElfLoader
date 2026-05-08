/-
Trust seam: every `@[extern]` declaration that crosses into the C
shims under `runtime/`, plus the `RuntimeOp` abstraction over those
externs and the IO interpreter that dispatches each constructor.

Three layers in this file:

  1. Externs (top half) — opaque `FileHandle`, mmap variants,
     mprotect, raw writes, ctor calls, exec/jump. A grep for
     `@[extern]` outside this file is a smell.

  2. `RuntimeOp` — pure data type describing every kernel call the
     loader makes, modulo the value-returning `mmapStack` and the
     no-return `execAndJump` (one-shot finalizers, called inline
     from `Main.realize`).

  3. `RuntimeOp.run` / `runAll` — IO interpreters; the only place
     in the codebase that calls externs.

The semantics of each extern match Linux `mmap(2)` / `mprotect(2)`.
Mappings live for the process lifetime; the kernel reclaims at exit.
Audited by inspection (~150 lines of C), not proven.

Bounds proofs live entirely on the Lean side (`Layout.patch_inRange`
etc.); externs take raw `UInt64` addresses and trust the caller has
done the math correctly. Pure planners (`Plan/Realize`,
`Plan/Reloc`, `Plan/Init`) emit `Array RuntimeOp`; the IO bookend
calls `RuntimeOp.runAll`.
-/

namespace LeanLoad

namespace Runtime

-- ============================================================================
-- FileHandle — a transparent kernel fd. The fd is held until process
-- exit; we never `close(2)` because `execAndJump` is non-returning
-- and the kernel reclaims at exit. Tests can construct arbitrary
-- handles (e.g. for synthetic fixtures); the kernel rejects invalid
-- fds at the syscall.
-- ============================================================================

def FileHandle : Type := UInt32
instance : Inhabited FileHandle := inferInstanceAs (Inhabited UInt32)

@[extern "leanload_open"]
opaque openFile (path : @& String) : IO FileHandle

@[extern "leanload_pread"]
opaque pread (h : FileHandle) (offset : UInt64) (len : UInt64) : IO ByteArray

/-- File-backed `MAP_PRIVATE | MAP_FIXED` overlay at `vaddr`. -/
@[extern "leanload_mmap_file"]
opaque mmap (h : FileHandle) (vaddr : UInt64) (len : UInt64)
    (prot : UInt32) (offset : UInt64) : IO Unit

-- ============================================================================
-- Memory ops — raw `UInt64` addresses.
-- ============================================================================

/-- Anonymous `MAP_FIXED` reservation at `vaddr` for `len` bytes. -/
@[extern "leanload_mmap_reserve"]
opaque mmapReserve (vaddr : UInt64) (len : UInt64) : IO Unit

/-- Anonymous `MAP_STACK` mapping; kernel chooses the address. Returns
    the chosen base — the caller threads it to `execAndJump`. -/
@[extern "leanload_mmap_stack"]
opaque mmapStack (len : UInt64) : IO UInt64

@[extern "leanload_mprotect"]
opaque mprotect (addr : UInt64) (len : UInt64) (prot : UInt32) : IO Unit

/-- Write 8 little-endian bytes of `value` at `addr`. -/
@[extern "leanload_patch64"]
opaque patch64 (addr : UInt64) (value : UInt64) : IO Unit

/-- Write the low 4 little-endian bytes of `value` at `addr`. -/
@[extern "leanload_patch32"]
opaque patch32 (addr : UInt64) (value : UInt64) : IO Unit

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

-- ============================================================================
-- PROT_* constants (Linux). The planner uses `PROT_WRITE` to widen
-- a file-backed segment's initial protection so partial-last-page
-- BSS can be zeroed before `mprotect` drops the bit for read-only
-- segments.
-- ============================================================================

def PROT_WRITE : UInt32 := 2

end Runtime

-- ============================================================================
-- RuntimeOp — pure abstraction over every fire-and-forget kernel
-- call. Pure planners emit `Array RuntimeOp`; `RuntimeOp.runAll`
-- dispatches each to the corresponding extern.
--
-- `mmapStack` (kernel-chosen address) and `execAndJump` (no-return
-- control transfer) stay outside this set — they don't fit the
-- fire-and-forget Unit-return shape and are one-shot finalizers
-- called inline from `Main.realize`.
-- ============================================================================

/-- One operation the loader asks the kernel to perform.
    Parameterised by `n`, the number of file handles available at IO
    time — `mmapFile`'s `fileIdx : Fin n` indexes into the
    caller-supplied handle table totally (no out-of-bounds failure
    mode at apply time). Other constructors don't use `n`, but the
    type still threads it for uniform `Array (RuntimeOp n)`. -/
inductive RuntimeOp (n : Nat) where
  /-- File-backed `MAP_PRIVATE | MAP_FIXED` overlay at `addr` for
      `len` bytes from `handles[fileIdx]`, file offset `offset`,
      protection `prot`. -/
  | mmapFile (fileIdx : Fin n) (addr len : UInt64)
             (prot : UInt32) (offset : UInt64)
  /-- Anonymous `MAP_FIXED` reservation at `addr` for `len` bytes. -/
  | mmapAnon (addr len : UInt64)
  /-- Zero `len` bytes at `addr`. -/
  | zeroout (addr len : UInt64)
  /-- Set protection on `[addr, addr+len)` to `prot`. -/
  | mprotect (addr len : UInt64) (prot : UInt32)
  /-- Write 8 little-endian bytes of `value` at `addr`. -/
  | patch64 (addr value : UInt64)
  /-- Write 4 little-endian bytes of `value` at `addr`. -/
  | patch32 (addr value : UInt64)
  /-- Call the constructor function at `addr`. -/
  | callCtor (addr : UInt64)

namespace RuntimeOp

/-- Interpret an op list in order. The `h_size` proof makes
    `handles[fileIdx]` total — no out-of-bounds case to handle. -/
def runAll {n : Nat} (handles : Array Runtime.FileHandle)
    (h_size : handles.size = n) (ops : Array (RuntimeOp n)) :
    IO Unit := ops.forM fun op =>
  match op with
  | .mmapFile idx addr len prot offset =>
    let h := handles[idx.val]'(h_size.symm ▸ idx.isLt)
    Runtime.mmap h addr len prot offset
  | .mmapAnon addr len      => Runtime.mmapReserve addr len
  | .zeroout addr len       => Runtime.zeroout addr len
  | .mprotect addr len prot => Runtime.mprotect addr len prot
  | .patch64 addr value     => Runtime.patch64 addr value
  | .patch32 addr value     => Runtime.patch32 addr value
  | .callCtor addr          => Runtime.callCtor addr

end RuntimeOp

end LeanLoad

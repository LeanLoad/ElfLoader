/-
Exec stage: the loader's IO bookend after the pure middle.

Pure planners (`Layout`, `Reloc`, `Init`) produce `Array MemoryOp` —
abstract data describing every kernel call the loader will make.
This file:

  1. Builds the per-region realize ops (`Region.ops`) — anon reserve,
     file overlay, partial-page zero, mprotect.
  2. Concatenates: realize ops ++ patch ops (from Reloc) ++ ctor ops.
  3. Interprets the op list via `runOp` — the only place that
     dispatches to `Runtime.*` externs.
  4. Allocates the kernel-style stack (kernel-chosen address) and
     `execAndJump`s to entry. Does not return.

Spec: gabi 08 § Process Initialization.
-/

import LeanLoad.Plan.Init
import LeanLoad.Plan.Layout
import LeanLoad.Plan.Reloc
import LeanLoad.MemoryOp
import LeanLoad.Runtime
import LeanLoad.Parse.Structs


namespace LeanLoad.Exec

open LeanLoad
open LeanLoad.Layout (Region)
open LeanLoad.Parse (RawPhdr)
open LeanLoad.Elaborate (Elf Segment)

-- ============================================================================
-- Pure: build the realize ops for one Region.
-- ============================================================================

/-- Ops to realize one `Region` from a file: anon reserve + file
    overlay + partial-page zero + final mprotect. Steps are
    conditional on the corresponding span being non-empty. -/
def Region.ops (handle : Runtime.FileHandle) (r : Region) : Array MemoryOp :=
  let ops : Array MemoryOp := #[.mmapAnon r.absVaddr r.length]
  let ops := if r.hasFileBacked then
    ops.push (.mmapFile handle r.absVaddr r.fileOverlayLen
                (r.prot ||| Runtime.PROT_WRITE) r.fileOffset)
  else ops
  let ops := if r.hasPartialBss then
    ops.push (.zeroout r.partialBssAddr r.partialBssLen)
  else ops
  ops.push (.mprotect r.absVaddr r.length r.prot)

/-- All realize ops for every elf's regions. -/
def realizeOps (elfs : Array Elf) (handles : Array Runtime.FileHandle)
    (h_size : handles.size = elfs.size)
    (bases : Array UInt64) (h_bases : bases.size = elfs.size) :
    Array MemoryOp := Id.run do
  let mut ops : Array MemoryOp := #[]
  for h : i in [:elfs.size] do
    let elf := elfs[i]
    let handle := handles[i]'(by rw [h_size]; exact h.upper)
    let base := bases[i]'(by rw [h_bases]; exact h.upper)
    for seg in elf.segments do
      ops := ops ++ Region.ops handle ⟨base, seg⟩
  return ops

/-- The full op list: realize ++ patches ++ ctors. -/
def planOps (elfs : Array Elf) (handles : Array Runtime.FileHandle)
    (h_size : handles.size = elfs.size)
    (bases : Array UInt64) (h_bases : bases.size = elfs.size)
    (patches : Array MemoryOp) (ctorAddrs : Array UInt64) : Array MemoryOp :=
  let ops := realizeOps elfs handles h_size bases h_bases
  let ops := ops ++ patches
  ops ++ ctorAddrs.map (.callCtor ·)

-- ============================================================================
-- IO interpreter — dispatches one op to the corresponding extern.
-- ============================================================================

def runOp : MemoryOp → IO Unit
  | .mmapFile h addr len prot offset => Runtime.mmap h addr len prot offset
  | .mmapAnon addr len               => Runtime.mmapReserve addr len
  | .zeroout addr len                => Runtime.zeroout addr len
  | .mprotect addr len prot          => Runtime.mprotect addr len prot
  | .patch64 addr value              => Runtime.patch64 addr value
  | .patch32 addr value              => Runtime.patch32 addr value
  | .callCtor addr                   => Runtime.callCtor addr

/-- Interpret an op list in order. -/
def runOps (ops : Array MemoryOp) : IO Unit :=
  ops.forM runOp

-- ============================================================================
-- One-shot finalizers: stack alloc + exec.
-- ============================================================================

/-- Stack size for the loaded program. Matches musl's default (8 MiB). -/
def stackBytes : UInt64 := 8 * 1024 * 1024

-- ============================================================================
-- Single IO bookend.
-- ============================================================================

/-- Plan all memory ops, run them, then build the kernel-style stack
    and jump. **Does not return.** -/
def realize (elfs : Array Elf) (handles : Array Runtime.FileHandle)
    (h_size : handles.size = elfs.size)
    (h_pos : 0 < elfs.size) (mainElf : Elf)
    (layouts : { a : Array Layout.ObjectLayout // a.size = elfs.size })
    (patches : Array MemoryOp)
    (ctorAddrs : Array UInt64)
    (path : String) : IO Unit := do
  let bases := layouts.val.map (·.base)
  have h_bases : bases.size = elfs.size := by simp [bases, layouts.property]
  let ops := planOps elfs handles h_size bases h_bases patches ctorAddrs
  runOps ops
  -- main is at index 0 by Discover convention.
  let mainBase := bases[0]'(by rw [h_bases]; exact h_pos)
  let mainEntry :=
    (layouts.val[0]'(by rw [layouts.property]; exact h_pos)).entry.getD 0
  let stackVa ← Runtime.mmapStack stackBytes
  let entry  := mainBase + mainEntry
  let phdrVa := mainBase + mainElf.phoff
  let phnum  := mainElf.phnum.toUInt64
  let phent  := Parse.RawPhdrSize.toUInt64
  Runtime.execAndJump entry phdrVa phent phnum 0 stackVa stackBytes path

end LeanLoad.Exec

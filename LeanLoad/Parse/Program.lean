/-
Program header table.

Spec: gabi 07 (`third_party/gabi/docsrc/elf/07-pheader.rst`).

The program header table is the load-time view of an ELF file: each entry
describes a segment the system needs to prepare the process image.
-/

import LeanLoad.Parse.Bytes

namespace LeanLoad.Parse.Program

open LeanLoad.Parse
open LeanLoad.Parse.Bytes

-- ============================================================================
-- Constants — gabi 07 § Program Header, Tables: Segment Types, Segment Flag Bits
-- ============================================================================

-- p_type
def PT_NULL    : UInt32 := 0
def PT_LOAD    : UInt32 := 1
def PT_DYNAMIC : UInt32 := 2
def PT_INTERP  : UInt32 := 3
def PT_NOTE    : UInt32 := 4
def PT_SHLIB   : UInt32 := 5
def PT_PHDR    : UInt32 := 6
def PT_TLS     : UInt32 := 7

-- p_flags (segment permission bits)
def PF_X : UInt32 := 0x1
def PF_W : UInt32 := 0x2
def PF_R : UInt32 := 0x4

#guard PT_LOAD = 1
#guard PT_DYNAMIC = 2
#guard PF_R + PF_W + PF_X = 7

-- ============================================================================
-- Program header — gabi 07 § Program Header Entry (Elf64_Phdr)
-- ============================================================================

/-- 64-bit program header entry. Layout matches `Elf64_Phdr` in gabi 07. -/
structure Header64 where
  p_type   : UInt32
  p_flags  : UInt32
  p_offset : UInt64
  p_vaddr  : UInt64
  p_paddr  : UInt64
  p_filesz : UInt64
  p_memsz  : UInt64
  p_align  : UInt64
  deriving Repr

/-- Size of one entry on disk (gabi 07: 4+4+8*6 = 56). -/
def entrySize : Nat := 56

#guard entrySize = 56

/-- Parse one program header entry at the current cursor. -/
def parse : Parser Header64 := do
  let p_type   ← u32le
  let p_flags  ← u32le
  let p_offset ← u64le
  let p_vaddr  ← u64le
  let p_paddr  ← u64le
  let p_filesz ← u64le
  let p_memsz  ← u64le
  let p_align  ← u64le
  return { p_type, p_flags, p_offset, p_vaddr, p_paddr, p_filesz, p_memsz, p_align }

/-- Parse `count` consecutive program-header entries starting at `offset`. -/
def parseTable (offset count : Nat) : Parser (Array Header64) :=
  parseArray offset count parse

end LeanLoad.Parse.Program

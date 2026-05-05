/-
The `.dynamic` array.

Spec: gabi 08 (`third_party/gabi/docsrc/elf/08-dynamic.rst`) § Dynamic Section.

Each entry is a (`d_tag`, `d_un`) pair. `d_tag` selects the interpretation
of `d_un` (either `d_val` — an integer — or `d_ptr` — a virtual address).
The array is terminated by a `DT_NULL` entry.
-/

import LeanLoad.Parse.Bytes

namespace LeanLoad.Parse.Dynamic

open LeanLoad.Parse
open LeanLoad.Parse.Bytes

-- ============================================================================
-- Constants — gabi 08 Table: Dynamic Array Tags
-- ============================================================================

def DT_NULL            : UInt64 := 0
def DT_NEEDED          : UInt64 := 1
def DT_PLTRELSZ        : UInt64 := 2
def DT_PLTGOT          : UInt64 := 3
def DT_HASH            : UInt64 := 4
def DT_STRTAB          : UInt64 := 5
def DT_SYMTAB          : UInt64 := 6
def DT_RELA            : UInt64 := 7
def DT_RELASZ          : UInt64 := 8
def DT_RELAENT         : UInt64 := 9
def DT_STRSZ           : UInt64 := 10
def DT_SYMENT          : UInt64 := 11
def DT_INIT            : UInt64 := 12
def DT_FINI            : UInt64 := 13
def DT_SONAME          : UInt64 := 14
def DT_RPATH           : UInt64 := 15
def DT_SYMBOLIC        : UInt64 := 16
def DT_REL             : UInt64 := 17
def DT_RELSZ           : UInt64 := 18
def DT_RELENT          : UInt64 := 19
def DT_PLTREL          : UInt64 := 20
def DT_DEBUG           : UInt64 := 21
def DT_TEXTREL         : UInt64 := 22
def DT_JMPREL          : UInt64 := 23
def DT_BIND_NOW        : UInt64 := 24
def DT_INIT_ARRAY      : UInt64 := 25
def DT_FINI_ARRAY      : UInt64 := 26
def DT_INIT_ARRAYSZ    : UInt64 := 27
def DT_FINI_ARRAYSZ    : UInt64 := 28
def DT_RUNPATH         : UInt64 := 29
def DT_FLAGS           : UInt64 := 30
def DT_PREINIT_ARRAY   : UInt64 := 32
def DT_PREINIT_ARRAYSZ : UInt64 := 33
def DT_SYMTAB_SHNDX    : UInt64 := 34

-- DT_FLAGS bits (gabi 08 Table: DT_FLAGS values)
def DF_ORIGIN     : UInt64 := 0x1
def DF_SYMBOLIC   : UInt64 := 0x2
def DF_TEXTREL    : UInt64 := 0x4
def DF_BIND_NOW   : UInt64 := 0x8
def DF_STATIC_TLS : UInt64 := 0x10

#guard DT_NULL = 0
#guard DT_NEEDED = 1
#guard DT_INIT_ARRAY = 25
#guard DT_RUNPATH = 29

-- ============================================================================
-- Dynamic entry — gabi 08 § Dynamic Section (Elf64_Dyn)
-- ============================================================================

/-- One entry of the `.dynamic` array. `d_un` holds either `d_val` or
    `d_ptr`; the interpretation is controlled by `d_tag` per gabi 08. -/
structure Dyn64 where
  d_tag : UInt64
  d_un  : UInt64
  deriving Repr, Inhabited

/-- Size of one entry on disk: two 8-byte fields. -/
def entrySize : Nat := 16

#guard entrySize = 16

/-- Parse a single `Elf64_Dyn` at the current cursor. -/
def parseEntry : Parser Dyn64 := do
  let d_tag ← u64le
  let d_un  ← u64le
  return { d_tag, d_un }

/-- Read entries up to and including `DT_NULL`, or until `limit` bytes
    have been consumed. `limit` is `(offset + p_filesz)` for the
    enclosing `PT_DYNAMIC` segment. -/
private partial def collect (limit : Nat) (acc : Array Dyn64) : Parser (Array Dyn64) := do
  let cur ← pos
  if cur >= limit then
    return acc
  let e ← parseEntry
  let acc := acc.push e
  if e.d_tag == DT_NULL then
    return acc
  collect limit acc

/-- Parse the `.dynamic` array. `offset` is the file offset (typically
    `p_offset` of the `PT_DYNAMIC` program header) and `bytes` is its
    `p_filesz`. -/
def parseTable (offset bytes : Nat) : Parser (Array Dyn64) := do
  seek offset
  collect (offset + bytes) (Array.mkEmpty 16)

-- ============================================================================
-- Convenience: lookup helpers over a parsed `.dynamic` table.
-- ============================================================================

/-- Find the first entry with the given tag. -/
def find? (tab : Array Dyn64) (tag : UInt64) : Option Dyn64 :=
  tab.find? (·.d_tag == tag)

/-- All entries matching a tag (e.g. all `DT_NEEDED`). -/
def findAll (tab : Array Dyn64) (tag : UInt64) : Array Dyn64 :=
  tab.filter (·.d_tag == tag)

end LeanLoad.Parse.Dynamic

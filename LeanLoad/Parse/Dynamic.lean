/-
The `.dynamic` array — bytes only.

Spec: gabi 08 (`third_party/gabi/docsrc/elf/08-dynamic.rst`) § Dynamic
Section.

Each entry is a (`d_tag`, `d_un`) pair. `d_tag` selects the
interpretation of `d_un` (either `d_val` — an integer — or `d_ptr` —
a virtual address); the array is terminated by a `DT_NULL` entry.

DT_* tag constants stay here because the `parse` stage uses them
*navigationally* (find DT_STRTAB / DT_SYMTAB / DT_RELA / … to know
where to read next). The semantic interpretation as a tagged-union
(d_un's meaning depends on d_tag) is `Elaborate`'s job.
-/

import LeanLoad.Parse.Bytes

namespace LeanLoad.Parse

-- ============================================================================
-- Navigational d_tag constants (used by `Parse.parse` to find sections).
-- Interpretive constants (DT_FLAGS, DF_*, the not-needed-for-parsing
-- subset of DT_*) live in `Elaborate`.
-- ============================================================================

def DT_NULL            : UInt64 := 0
def DT_NEEDED          : UInt64 := 1
def DT_PLTRELSZ        : UInt64 := 2
def DT_HASH            : UInt64 := 4
def DT_STRTAB          : UInt64 := 5
def DT_SYMTAB          : UInt64 := 6
def DT_RELA            : UInt64 := 7
def DT_RELASZ          : UInt64 := 8
def DT_STRSZ           : UInt64 := 10
def DT_SONAME          : UInt64 := 14
def DT_RPATH           : UInt64 := 15
def DT_JMPREL          : UInt64 := 23
def DT_INIT_ARRAY      : UInt64 := 25
def DT_INIT_ARRAYSZ    : UInt64 := 27
def DT_RUNPATH         : UInt64 := 29

-- GNU extension (gnu-gabi `program-loading-and-dynamic-linking.txt`
-- § Hashes). Faster hash format than `DT_HASH`. Modern GNU/Linux
-- toolchains often emit this instead of `DT_HASH`.
def DT_GNU_HASH        : UInt64 := 0x6ffffef5

/-- Raw `.dynamic` entry — gabi 08 § Dynamic Section (Elf64_Dyn).
    `d_un` holds either `d_val` or `d_ptr`; interpretation is
    `Elaborate`'s job. -/
structure RawDyn where
  d_tag : UInt64
  d_un  : UInt64
  deriving Repr, Inhabited

namespace RawDyn

/-- Size of one entry on disk: two 8-byte fields. -/
def entrySize : Nat := 16

end RawDyn

end LeanLoad.Parse

-- ============================================================================
-- Byte-level parser + lookup helpers.
-- ============================================================================

namespace LeanLoad.Parse.Dynamic

open LeanLoad.Parse
open LeanLoad.Parse.Bytes

/-- Parse a single `Elf64_Dyn` at the current cursor. -/
def parseEntry : Parser RawDyn := do
  let d_tag ← u64le
  let d_un  ← u64le
  return { d_tag, d_un }

/-- Read entries up to and including `DT_NULL`, or until `limit` bytes
    have been consumed. -/
private def collect (fuel : Nat) (limit : Nat) (acc : Array RawDyn) :
    Parser (Array RawDyn) := do
  match fuel with
  | 0 => return acc
  | fuel + 1 =>
    let cur ← pos
    if cur >= limit then
      return acc
    let e ← parseEntry
    let acc := acc.push e
    if e.d_tag == DT_NULL then
      return acc
    collect fuel limit acc

/-- Parse the `.dynamic` array. `offset` is the file offset (typically
    `p_offset` of the `PT_DYNAMIC` program header) and `bytes` is its
    `p_filesz`. -/
def parseTable (offset bytes : Nat) : Parser (Array RawDyn) := do
  seek offset
  collect bytes (offset + bytes) (Array.mkEmpty 16)

/-- Find the first entry with the given tag. -/
def find? (tab : Array RawDyn) (tag : UInt64) : Option RawDyn :=
  tab.find? (·.d_tag == tag)

/-- All entries matching a tag (e.g. all `DT_NEEDED`). -/
def findAll (tab : Array RawDyn) (tag : UInt64) : Array RawDyn :=
  tab.filter (·.d_tag == tag)

section Example
private def tab : Array RawDyn := #[
  { d_tag := DT_NEEDED, d_un := 0x10 },
  { d_tag := DT_RUNPATH, d_un := 0x20 },
  { d_tag := DT_NEEDED, d_un := 0x30 },
  { d_tag := DT_NEEDED, d_un := 0x40 },
  { d_tag := DT_NULL,   d_un := 0 } ]

#guard (find? tab DT_NEEDED).map (·.d_un)  = some 0x10
#guard (find? tab DT_RUNPATH).map (·.d_un) = some 0x20
#guard  find? tab DT_HASH                  = none

#guard (findAll tab DT_NEEDED).map (·.d_un) = #[0x10, 0x30, 0x40]
#guard (findAll tab DT_HASH).size           = 0
end Example

end LeanLoad.Parse.Dynamic

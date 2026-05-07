/-
String tables — bytes only.

Spec: gabi 04 (`third_party/gabi/docsrc/elf/04-strtab.rst`) § String Table.

A string table is a contiguous byte buffer of NUL-terminated C strings;
entries are referenced by their byte offset (`st_name` in symbol entries,
`d_un` for `DT_SONAME`/`DT_NEEDED`/`DT_RUNPATH` in the dynamic array, …).
Offset 0 is reserved for the empty string.

Type + lookup + byte-level reader, all in one file. The `lookup`
operation is data, not a check, so it lives here.
-/

import LeanLoad.Parse.Bytes

namespace LeanLoad.Parse

/-- A string table is just a byte buffer; entries are null-terminated
    C strings indexed by byte offset. -/
abbrev RawStrtab := ByteArray

namespace RawStrtab

/-- Read the null-terminated string at `offset` in `tab`. Returns
    `none` if `offset` is past the end. The result excludes the null. -/
def lookup (tab : RawStrtab) (offset : Nat) : Option String :=
  if offset >= tab.size then
    none
  else
    let endIdx := tab.findIdx? (· == 0) offset |>.getD tab.size
    String.fromUTF8? (tab.extract offset endIdx)

section Example
private def t : RawStrtab :=
  ⟨#[0,
     'p'.toNat.toUInt8, 'r'.toNat.toUInt8, 'i'.toNat.toUInt8,
     'n'.toNat.toUInt8, 't'.toNat.toUInt8, 'f'.toNat.toUInt8, 0,
     'p'.toNat.toUInt8, 'u'.toNat.toUInt8, 't'.toNat.toUInt8,
     's'.toNat.toUInt8, 0]⟩

#guard lookup t 0  = some ""
#guard lookup t 1  = some "printf"
#guard lookup t 8  = some "puts"
#guard lookup t 13 = none
#guard lookup t 99 = none
#guard lookup t 4  = some "ntf"
end Example

end RawStrtab

end LeanLoad.Parse

namespace LeanLoad.Parse.StringTable

open LeanLoad.Parse
open LeanLoad.Parse.Bytes

/-- Read a string table out of the file: `offset .. offset+size`. -/
def parse (offset size : Nat) : Parser RawStrtab := do
  seek offset
  slice size

end LeanLoad.Parse.StringTable

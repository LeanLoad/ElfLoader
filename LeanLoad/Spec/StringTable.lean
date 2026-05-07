/-
String tables — gabi 04 spec.

Spec: gabi 04 (`third_party/gabi/docsrc/elf/04-strtab.rst`) § String Table.

A string table is a contiguous byte buffer of NUL-terminated C strings;
entries are referenced by their byte offset (`st_name` in symbol entries,
`d_un` for `DT_SONAME`/`DT_NEEDED`/`DT_RUNPATH` in the dynamic array, …).
Offset 0 is reserved for the empty string.

Type only — parser in `LeanLoad.Parse.StringTable`.
-/

namespace LeanLoad.Spec.StringTable

/-- A string table is just a byte buffer; entries are null-terminated
    C strings indexed by byte offset. -/
abbrev StringTable := ByteArray

/-- Read the null-terminated string at `offset` in `tab`. Returns
    `none` if `offset` is past the end. The result excludes the null. -/
def lookup (tab : StringTable) (offset : Nat) : Option String :=
  if offset >= tab.size then
    none
  else
    let endIdx := tab.findIdx? (· == 0) offset |>.getD tab.size
    String.fromUTF8? (tab.extract offset endIdx)

section Example
-- Synthetic strtab: "\0printf\0puts\0".
-- offsets:           0  1     7    12
private def t : StringTable :=
  ⟨#[0,
     'p'.toNat.toUInt8, 'r'.toNat.toUInt8, 'i'.toNat.toUInt8,
     'n'.toNat.toUInt8, 't'.toNat.toUInt8, 'f'.toNat.toUInt8, 0,
     'p'.toNat.toUInt8, 'u'.toNat.toUInt8, 't'.toNat.toUInt8,
     's'.toNat.toUInt8, 0]⟩

#guard lookup t 0  = some ""           -- offset 0 reserved for empty
#guard lookup t 1  = some "printf"
#guard lookup t 8  = some "puts"
#guard lookup t 13 = none               -- past the end
#guard lookup t 99 = none               -- way past the end
-- Reading mid-string yields the suffix from that offset to the next NUL.
#guard lookup t 4  = some "ntf"
end Example

end LeanLoad.Spec.StringTable

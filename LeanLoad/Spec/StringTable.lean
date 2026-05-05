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

end LeanLoad.Spec.StringTable

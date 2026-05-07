/-
Dynamic string-table lookup.

Spec: gabi 04 (`third_party/gabi/docsrc/elf/04-strtab.rst`) § String
Table — null-terminated bytes addressed by an offset into the table;
offset 0 always denotes either the empty string or "no name".

UTF-8 decode is *not* in gabi (which says "byte sequence"); LeanLoad
treats the bytes as UTF-8 and returns `none` on decode failure, which
is consistent with how every Linux toolchain emits names.

`RawStrtab` is `Parse.RawStrtab` (an alias for `ByteArray`). Lookup
is interpretive — hence `Elaborate`, not `Parse`. The function lives
in `Parse.RawStrtab`'s own namespace so dot notation
(`tab.lookup off`) resolves.
-/

import LeanLoad.Parse.Structs

namespace LeanLoad.Parse.RawStrtab

/-- Read the null-terminated string at `offset` in `tab`. Returns
    `none` if `offset` is past the end or if the bytes don't decode
    as UTF-8. The result excludes the null. -/
def lookup (tab : RawStrtab) (offset : Nat) : Option String :=
  if offset >= tab.size then
    none
  else
    let endIdx := tab.findIdx? (· == 0) offset |>.getD tab.size
    String.fromUTF8? (tab.extract offset endIdx)

section Example
private def t : RawStrtab := "\x00printf\x00puts\x00".toUTF8

#guard lookup t 0  = some ""
#guard lookup t 1  = some "printf"
#guard lookup t 8  = some "puts"
#guard lookup t 13 = none
#guard lookup t 99 = none
#guard lookup t 4  = some "ntf"
end Example

end LeanLoad.Parse.RawStrtab

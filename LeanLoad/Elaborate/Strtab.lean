/-
Dynamic string-table lookup.

`RawStrtab` is `Parse.RawStrtab` (an alias for `ByteArray`); reading a
null-terminated UTF-8 string out of it can fail (offset out of range,
or bytes that don't decode), which makes it interpretive — hence
`Elaborate`, not `Parse`. The function lives in `Parse.RawStrtab`'s
own namespace so dot notation (`tab.lookup off`) resolves.
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

/-
gabi 04 § String Table — `RawStrtab` is a byte buffer holding
NUL-terminated C strings addressed by byte offset; offset 0 always
denotes either the empty string or "no name".

`lookup` reads bytes between an offset and the next NUL and decodes
them as UTF-8. gabi specifies the table as "byte sequence" — UTF-8
is LeanLoad's interpretation, consistent with how every Linux
toolchain emits names. Returns `none` on out-of-range offset or
decode failure.
-/

namespace LeanLoad.Parse

abbrev RawStrtab := ByteArray

/-- Read the null-terminated string at `offset` in `tab`. Returns
    `none` if `offset` is past the end or if the bytes don't decode
    as UTF-8. The result excludes the null. Defined under the
    `RawStrtab` namespace prefix so dot notation `tab.lookup off`
    resolves. -/
def RawStrtab.lookup (tab : RawStrtab) (offset : Nat) : Option String :=
  if offset >= tab.size then
    none
  else
    let endIdx := tab.findIdx? (· == 0) offset |>.getD tab.size
    String.fromUTF8? (tab.extract offset endIdx)

/-- 32-byte string-table fixture holding four NUL-terminated names.
    Coordinated with the consolidated `Parse.RawElf.fixtureBytes`: the
    consumed entries are pointed at by `DT_NEEDED` (→ "libc.so.6"),
    `DT_SONAME` (→ "mylib.so"), `DT_RUNPATH` (→ "lib"), and
    `RawSym.fixtureBytes`'s second symbol's `st_name` (→ "printf").
    Real `.dynstr` always starts with a NUL byte so offset 0 means
    "empty string". -/
def RawStrtab.fixtureBytes : RawStrtab := ⟨#[
  0x00,                                                         -- [0x00] NUL
  0x6c, 0x69, 0x62, 0x63, 0x2e, 0x73, 0x6f, 0x2e, 0x36, 0x00,   -- [0x01] "libc.so.6\0"
  0x70, 0x72, 0x69, 0x6e, 0x74, 0x66, 0x00,                     -- [0x0b] "printf\0"
  0x6d, 0x79, 0x6c, 0x69, 0x62, 0x2e, 0x73, 0x6f, 0x00,         -- [0x12] "mylib.so\0"
  0x6c, 0x69, 0x62, 0x00,                                       -- [0x1b] "lib\0"
  0x00                                                          -- [0x1f] pad
]⟩

#guard RawStrtab.fixtureBytes.size == 32

section Example

open RawStrtab

-- ── Byte-level layout ───────────────────────────────────────────────
-- Each string starts at its documented byte offset.
#guard fixtureBytes[0x00]? = some 0x00  -- the mandatory empty-string NUL
#guard fixtureBytes[0x01]? = some 0x6c  -- 'l' of "libc.so.6"
#guard fixtureBytes[0x0b]? = some 0x70  -- 'p' of "printf"
#guard fixtureBytes[0x12]? = some 0x6d  -- 'm' of "mylib.so"
#guard fixtureBytes[0x1b]? = some 0x6c  -- 'l' of "lib"

-- ── `lookup` over canonical offsets ─────────────────────────────────
#guard lookup fixtureBytes 0x00 = some ""           -- empty string at 0
#guard lookup fixtureBytes 0x01 = some "libc.so.6"
#guard lookup fixtureBytes 0x0b = some "printf"
#guard lookup fixtureBytes 0x12 = some "mylib.so"
#guard lookup fixtureBytes 0x1b = some "lib"

-- Mid-string offsets: gabi allows them (the trailing suffix is a valid
-- entry too — the NUL ends *any* lookup starting before it).
#guard lookup fixtureBytes 0x04 = some "c.so.6"

-- ── Out-of-range / past-end ─────────────────────────────────────────
#guard lookup fixtureBytes 32  = none   -- exactly at size
#guard lookup fixtureBytes 99  = none   -- way past

end Example

end LeanLoad.Parse

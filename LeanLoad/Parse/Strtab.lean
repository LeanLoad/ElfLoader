/-
gabi 04 § String Table — `Strtab` is a byte buffer holding
NUL-terminated C strings addressed by byte offset; offset 0 always
denotes either the empty string or "no name".

`lookup` reads bytes between an offset and the next NUL and decodes
them as UTF-8. gabi specifies the table as "byte sequence" — UTF-8
is LeanLoad's interpretation, consistent with how every Linux
toolchain emits names. Returns `none` on out-of-range offset or
decode failure.

The lookup-offset parameter is typed `StrtabOff` (see
`Parse/Address.lean`) — a distinct nominal wrapper over `UInt64`.
That makes accidental confusion with a `Eaddr` or file offset a
type error rather than a silent runtime mis-read.
-/

import LeanLoad.Parse.Basic
import LeanLoad.Parse.Decode.Decoder

namespace LeanLoad.Parse

abbrev Strtab := ByteArray

instance : Repr Strtab where
  reprPrec tab prec := reprPrec tab.data prec

namespace Strtab

/-- Empty string table when `DT_STRTAB`/`DT_STRSZ` is absent. Any nonzero
    string reference will fail later through `Strtab.entry`. -/
def empty : Strtab := ByteArray.mk #[]

/-- Decode a string table: preserve bytes exactly. gabi 04 string tables have
    no fixed-width record structure; offsets are validated by `lookup`. -/
def decode : Decoder Strtab := Decoder.buffer

end Strtab

/-- Read the null-terminated string at `offset` in `tab`. Returns
    `none` if `offset` is past the end or if the bytes don't decode
    as UTF-8. The result excludes the null. Defined under the
    `Strtab` namespace prefix so dot notation `tab.lookup off`
    resolves. -/
def Strtab.lookup (tab : Strtab) (offset : StrtabOff) : Option String :=
  let o := offset.toNat
  if o >= tab.size then
    none
  else
    let endIdx := tab.findIdx? (· == 0) o |>.getD tab.size
    String.fromUTF8? (tab.extract o endIdx)

/-- A string-table offset resolved against a concrete string table.
    `value` is the decoded string and `lookup_eq` witnesses that the
    offset is valid for this table under LeanLoad's UTF-8
    interpretation of gabi 04 string-table bytes. -/
structure StrtabEntry (tab : Strtab) where
  off       : StrtabOff
  value     : String
  lookup_eq : Strtab.lookup tab off = some value

/-- Resolve an offset into a witnessed string-table entry. -/
def Strtab.entry (tab : Strtab) (off : StrtabOff) : Except String (StrtabEntry tab) :=
  match h : Strtab.lookup tab off with
  | some value => .ok { off, value, lookup_eq := h }
  | none       =>
      .error s!"invalid strtab offset 0x{off.toNat} (strtab size {tab.size})"

/-- Resolve an offset to its string value, preserving dynamic-tag context in
    diagnostics. -/
def Strtab.resolve (tab : Strtab) (label : String) (off : StrtabOff) : Except String String :=
  match tab.entry off with
  | .ok entry => .ok entry.value
  | .error e  => .error s!"parse: {label}: {e}"

/-- Resolve an optional dynamic string-table offset. Missing tags stay missing;
    present malformed offsets are reported with the tag label. -/
def Strtab.resolve? (tab : Strtab) (label : String) :
    Option StrtabOff → Except String (Option String)
  | none     => .ok none
  | some off => do
      let s ← tab.resolve label off
      pure (some s)

/-- 32-byte string-table fixture holding four NUL-terminated names.
    Coordinated with the consolidated `Parse.Examples.fixtureBytes`: the
    consumed entries are pointed at by `DT_NEEDED` (→ "libc.so.6"),
    `DT_SONAME` (→ "mylib.so"), `DT_RUNPATH` (→ "lib"), and
    `RawSym.fixtureBytes`'s second symbol's `st_name` (→ "printf").
    Real `.dynstr` always starts with a NUL byte so offset 0 means
    "empty string". -/
def Strtab.fixtureBytes : Strtab := ⟨#[
  0x00,                                                         -- [0x00] NUL
  0x6c, 0x69, 0x62, 0x63, 0x2e, 0x73, 0x6f, 0x2e, 0x36, 0x00,   -- [0x01] "libc.so.6\0"
  0x70, 0x72, 0x69, 0x6e, 0x74, 0x66, 0x00,                     -- [0x0b] "printf\0"
  0x6d, 0x79, 0x6c, 0x69, 0x62, 0x2e, 0x73, 0x6f, 0x00,         -- [0x12] "mylib.so\0"
  0x6c, 0x69, 0x62, 0x00,                                       -- [0x1b] "lib\0"
  0x00                                                          -- [0x1f] pad
]⟩

#guard Strtab.fixtureBytes.size == 32

section Example

open Strtab

-- ── Byte-level layout ───────────────────────────────────────────────
-- Each string starts at its documented byte offset.
#guard fixtureBytes[0x00]? = some 0x00  -- the mandatory empty-string NUL
#guard fixtureBytes[0x01]? = some 0x6c  -- 'l' of "libc.so.6"
#guard fixtureBytes[0x0b]? = some 0x70  -- 'p' of "printf"
#guard fixtureBytes[0x12]? = some 0x6d  -- 'm' of "mylib.so"
#guard fixtureBytes[0x1b]? = some 0x6c  -- 'l' of "lib"

-- ── `lookup` over canonical offsets ─────────────────────────────────
-- Numeric literals in `StrtabOff` position resolve via `OfNat`.
#guard lookup fixtureBytes (0x00 : StrtabOff) = some ""           -- empty string at 0
#guard lookup fixtureBytes (0x01 : StrtabOff) = some "libc.so.6"
#guard lookup fixtureBytes (0x0b : StrtabOff) = some "printf"
#guard lookup fixtureBytes (0x12 : StrtabOff) = some "mylib.so"
#guard lookup fixtureBytes (0x1b : StrtabOff) = some "lib"

#guard
  match fixtureBytes.entry (0x0b : StrtabOff) with
  | .ok e    => e.value == "printf"
  | .error _ => false

#guard
  match fixtureBytes.resolve "DT_NEEDED" (0x01 : StrtabOff) with
  | .ok s    => s == "libc.so.6"
  | .error _ => false

#guard
  match fixtureBytes.resolve? "DT_SONAME" (some (0x12 : StrtabOff)) with
  | .ok (some s) => s == "mylib.so"
  | _            => false

-- Mid-string offsets: gabi allows them (the trailing suffix is a valid
-- entry too — the NUL ends *any* lookup starting before it).
#guard lookup fixtureBytes (0x04 : StrtabOff) = some "c.so.6"

-- ── Out-of-range / past-end ─────────────────────────────────────────
#guard lookup fixtureBytes (32 : StrtabOff) = none   -- exactly at size
#guard lookup fixtureBytes (99 : StrtabOff) = none   -- way past

#guard
  match fixtureBytes.entry (32 : StrtabOff) with
  | .ok _    => false
  | .error _ => true

end Example

end LeanLoad.Parse

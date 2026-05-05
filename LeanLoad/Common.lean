/-
`LeanLoad.Common` — small helpers shared across modules.

Lean-side analogue of `runtime/common.h`. Keep the surface tiny;
broader topical utilities should live next to the module that uses
them, not here.
-/

namespace LeanLoad

/-- Hex string of a `Nat` — lowercase, no `0x` prefix, no leading zero
    padding. Used by `--inspect` output. -/
def Nat.hex (n : Nat) : String :=
  String.ofList (Nat.toDigits 16 n)

#guard Nat.hex 0 = "0"
#guard Nat.hex 0x4000b0 = "4000b0"
#guard Nat.hex 0xdeadbeef = "deadbeef"

/-- Serialize a `UInt64` as 8 little-endian bytes. -/
def UInt64.toLEBytes (x : UInt64) : ByteArray :=
  ByteArray.mk #[
    (x &&& 0xff).toUInt8,
    ((x >>> 8) &&& 0xff).toUInt8,
    ((x >>> 16) &&& 0xff).toUInt8,
    ((x >>> 24) &&& 0xff).toUInt8,
    ((x >>> 32) &&& 0xff).toUInt8,
    ((x >>> 40) &&& 0xff).toUInt8,
    ((x >>> 48) &&& 0xff).toUInt8,
    ((x >>> 56) &&& 0xff).toUInt8 ]

/-- Serialize the low 32 bits of a `UInt64` as 4 little-endian bytes. -/
def UInt64.toLEBytes32 (x : UInt64) : ByteArray :=
  ByteArray.mk #[
    (x &&& 0xff).toUInt8,
    ((x >>> 8) &&& 0xff).toUInt8,
    ((x >>> 16) &&& 0xff).toUInt8,
    ((x >>> 24) &&& 0xff).toUInt8 ]

#guard (UInt64.toLEBytes 0x1122334455667788).toList == [0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11]
#guard (UInt64.toLEBytes32 0x12345678).toList == [0x78, 0x56, 0x34, 0x12]

end LeanLoad

/-
Canonical byte decoders for typed values.
-/

import LeanLoad.Parse.Decode.Decoder

namespace LeanLoad.Parse

/-- A fixed-width type with a canonical byte decoder. Runtime-sized tables and
    blobs use explicit `Decoder` values instead of a `Decodable` instance. -/
class Decodable (α : Type) where
  byteSize : Nat
  decode : Decoder α

namespace Decodable

/-- Decode exactly `count` fixed-width entries. -/
def decodeArray [Decodable α] (count : Nat) : Decoder (Array α) :=
  Decoder.array count (Decodable.decode (α := α))

/-- Parse one fixed-width value from a byte buffer. -/
def parse [Decodable α] (bytes : ByteArray) : Except String α :=
  Decoder.run bytes (Decodable.decode (α := α))

/-- Parse exactly `count` fixed-width values from a byte buffer. -/
def parseArray [Decodable α] (bytes : ByteArray) (count : Nat) : Except String (Array α) :=
  Decoder.run bytes (decodeArray (α := α) count)

/-- Check a proof field while decoding. Derived decoders use this for `Prop`
    fields: earlier decoded fields determine the proposition; failure reports the
    field label. -/
def require (label : String) (p : Prop) [Decidable p] : Decoder (PLift p) := do
  if h : p then
    return ⟨h⟩
  else
    throw s!"decode: proof field {label} failed"

end Decodable

instance : Decodable UInt8 where
  byteSize := 1
  decode := Decoder.u8

instance : Decodable UInt16 where
  byteSize := 2
  decode := Decoder.u16le

instance : Decodable UInt32 where
  byteSize := 4
  decode := Decoder.u32le

instance : Decodable UInt64 where
  byteSize := 8
  decode := Decoder.u64le

#guard
  match Decodable.parse (α := UInt8) (ByteArray.mk #[0x12]) with
  | .ok 0x12 => true
  | _        => false

#guard (Decodable.parseArray (α := UInt8) (ByteArray.mk #[0x12, 0x34]) 2).toOption =
  some #[0x12, 0x34]

/-- Semantic decoding from an on-disk scalar to a typed field.

    Closed enums return an error for unknown values; open namespaces and
    sentinel-carrying fields can classify every raw value. -/
class DecodableFromScalar (α : Type) (Backing : outParam Type) where
  fromScalar : Backing → Except String α

/-- `Decodable α` derived from `DecodableFromScalar`: decode the backing scalar and
    classify it, surfacing classifier failures as decoder failures. -/
instance [M : DecodableFromScalar α Backing] [Decodable Backing] : Decodable α where
  byteSize := Decodable.byteSize (α := Backing)
  decode := do
    let raw : Backing ← Decodable.decode (α := Backing)
    match M.fromScalar raw with
    | .ok v     => return v
    | .error e  => throw e

end LeanLoad.Parse

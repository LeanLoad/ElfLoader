/-
Canonical byte decoders for typed values.
-/

import LeanLoad.Basic
import LeanLoad.Parse.Decode.Decoder

namespace LeanLoad.Parse

/-- A fixed-width raw type with a canonical byte decoder. Runtime-sized tables,
    blobs, and checked proof-carrying types use explicit `Decoder` values instead
    of a `Decodable` instance. -/
class Decodable (α : Type) where
  byteSize : ByteSize
  decoder : Decoder α

namespace Decodable

/-- Cursor-level decoder for exactly `count` fixed-width entries. -/
def arrayDecoder [Decodable α] (count : Nat) : Decoder (Array α) :=
  Decoder.array count (Decodable.decoder (α := α))

/-- Decode one fixed-width value from a byte buffer. -/
def decode [Decodable α] (bytes : ByteArray) : Except String α :=
  (Decodable.decoder (α := α)).decode bytes

/-- Decode exactly `count` fixed-width values from a byte buffer. -/
def decodeArray [Decodable α] (bytes : ByteArray) (count : Nat) : Except String (Array α) :=
  (arrayDecoder (α := α) count).decode bytes

end Decodable

instance : Decodable UInt8 where
  byteSize := 1
  decoder := Decoder.u8

instance : Decodable UInt16 where
  byteSize := 2
  decoder := Decoder.u16le

instance : Decodable UInt32 where
  byteSize := 4
  decoder := Decoder.u32le

instance : Decodable UInt64 where
  byteSize := 8
  decoder := Decoder.u64le

#guard
  match Decodable.decode (α := UInt8) (ByteArray.mk #[0x12]) with
  | .ok 0x12 => true
  | _        => false

#guard (Decodable.decodeArray (α := UInt8) (ByteArray.mk #[0x12, 0x34]) 2).toOption =
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
  decoder := do
    let raw : Backing ← Decodable.decoder (α := Backing)
    match M.fromScalar raw with
    | .ok v     => return v
    | .error e  => throw e

end LeanLoad.Parse

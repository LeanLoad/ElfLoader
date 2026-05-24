/-
Canonical byte decoders for typed values.
-/

import LeanLoad.Parse.Decode.Decoder

namespace LeanLoad.Parse

/-- A fixed-width type with a canonical byte decoder. Runtime-sized tables and
    blobs use explicit `Decoder` values instead of a `Decodable` instance. -/
class Decodable (α : Type) where
  byteSize : Nat
  decoder : Decoder α

namespace Decodable

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

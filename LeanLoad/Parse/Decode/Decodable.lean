/-
Canonical byte decoders for typed values.
-/

import LeanLoad.Parse.Decode.Decoder

namespace LeanLoad.Parse

/-- A type with a canonical byte decoder. The decoder may also check and
    construct proof fields required by `α`. -/
class Decodable (α : Type) where
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

instance : Decodable UInt8  := ⟨Decoder.u8⟩
instance : Decodable UInt16 := ⟨Decoder.u16le⟩
instance : Decodable UInt32 := ⟨Decoder.u32le⟩
instance : Decodable UInt64 := ⟨Decoder.u64le⟩

/-- Semantic decoding from an on-disk scalar to a typed field.

    Closed enums return an error for unknown values; open namespaces and
    sentinel-carrying fields can classify every raw value. -/
class DecodableFromScalar (α : Type) (Backing : outParam Type) where
  fromScalar : Backing → Except String α

/-- `Decodable α` derived from `DecodableFromScalar`: decode the backing scalar and
    classify it, surfacing classifier failures as decoder failures. -/
instance [M : DecodableFromScalar α Backing] [Decodable Backing] : Decodable α where
  decoder := do
    let raw : Backing ← Decodable.decoder
    match M.fromScalar raw with
    | .ok v     => return v
    | .error e  => throw e

end LeanLoad.Parse

/-
Reusable byte-buffer decoder computations.

Endianness is fixed to little-endian: gABI 02 § ELF Identification permits
either byte order, and LeanLoad rejects unsupported `EI_DATA` values in the
typed ELF header before later stages consume decoded fields.
-/

namespace LeanLoad.Parse

namespace Decoder

structure State where
  bytes : ByteArray
  pos   : Nat

instance : Repr State where
  reprPrec s prec := reprPrec (s.bytes.data, s.pos) prec

end Decoder

abbrev Decoder (α : Type) : Type := StateT Decoder.State (Except String) α

namespace Decoder

/-- Decode a whole byte buffer with this decoder. -/
def decode (decoder : Decoder α) (bytes : ByteArray) : Except String α :=
  Prod.fst <$> StateT.run decoder ({ bytes, pos := 0 } : State)

/-- Decode a whole byte buffer with this decoder, returning `none` on failure.
    Intended for examples and `#guard`s. -/
def decode? (decoder : Decoder α) (bytes : ByteArray) : Option α :=
  (decoder.decode bytes).toOption

/-- Read one byte. Fails on EOF. -/
def u8 : Decoder UInt8 := do
  let s ← get
  if s.pos < s.bytes.size then
    set { s with pos := s.pos + 1 }
    return s.bytes[s.pos]!
  else
    throw s!"u8: EOF at offset {s.pos}/{s.bytes.size}"

/-- Read a little-endian 16-bit unsigned. -/
def u16le : Decoder UInt16 := do
  let lo ← u8
  let hi ← u8
  return lo.toUInt16 ||| (hi.toUInt16 <<< 8)

/-- Read a little-endian 32-bit unsigned. -/
def u32le : Decoder UInt32 := do
  let lo ← u16le
  let hi ← u16le
  return lo.toUInt32 ||| (hi.toUInt32 <<< 16)

/-- Read a little-endian 64-bit unsigned. -/
def u64le : Decoder UInt64 := do
  let lo ← u32le
  let hi ← u32le
  return lo.toUInt64 ||| (hi.toUInt64 <<< 32)

/-- Return the decoder's entire input buffer without changing the cursor. -/
def buffer : Decoder ByteArray := return (← get).bytes

/-- Decode exactly `count` consecutive entries with `decoder`. -/
def array (count : Nat) (decoder : Decoder α) : Decoder (Array α) := do
  let mut entries : Array α := Array.mkEmpty count
  for _ in [:count] do
    entries := entries.push (← decoder)
  return entries

section Example

#guard u8.decode? (ByteArray.mk #[0x12]) == some 0x12
#guard u16le.decode? (ByteArray.mk #[0x34, 0x12]) == some 0x1234
#guard u32le.decode? (ByteArray.mk #[0x78, 0x56, 0x34, 0x12]) == some 0x12345678

end Example

end Decoder

end LeanLoad.Parse

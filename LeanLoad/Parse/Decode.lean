/-
Parser monad and byte-decode infrastructure.

Three layers, all in the `LeanLoad.Parse` namespace:

1. **Parser monad** — `StateT State (Except String)`. A read cursor
   over a `ByteArray` that may fail with a string error.

2. **Byte primitives** — fixed-width little-endian reads (`u8`,
   `u16le`, `u32le`, `u64le`), cursor moves (`pos`/`seek`/`skip`),
   and exact-bytes match (`expect`).

3. **`BytesDecode α`** — type-driven dispatch. Primitive instances
   for `UInt8/16/32/64`, plus `Pad n` (skip) and `Magic bs` (verify).
   Per-struct instances are auto-derived (see `Parse/Deriving.lean`).
   `decodeArray` reads `count` entries via the typeclass.

Endianness is fixed to little-endian — gabi 02 § ELF Identification
allows either, but LeanLoad targets x86-64 / AArch64 (both LE); the
`ei_data` semantic check rejects big-endian inputs at `elaborate`.
-/

namespace LeanLoad.Parse

-- ============================================================================
-- Parser monad
-- ============================================================================

structure State where
  bytes : ByteArray
  pos   : Nat

abbrev Parser (α : Type) : Type := StateT State (Except String) α

def Parser.run (b : ByteArray) (p : Parser α) : Except String α :=
  Prod.fst <$> StateT.run p ({ bytes := b, pos := 0 } : State)

-- ============================================================================
-- Byte primitives
-- ============================================================================

/-- Current cursor offset. -/
def cursor : Parser Nat := return (← get).pos

/-- Move the cursor to an absolute offset. -/
def seek (off : Nat) : Parser Unit := modify ({ · with pos := off })

/-- Skip `n` bytes from the current position. -/
def skip (n : Nat) : Parser Unit := modify (fun s => { s with pos := s.pos + n })

/-- Read one byte. Fails on EOF. -/
def u8 : Parser UInt8 := do
  let s ← get
  if s.pos < s.bytes.size then
    set { s with pos := s.pos + 1 }
    return s.bytes[s.pos]!
  else
    throw s!"u8: EOF at offset {s.pos}/{s.bytes.size}"

/-- Read a little-endian 16-bit unsigned. -/
def u16le : Parser UInt16 := do
  let lo ← u8; let hi ← u8
  return lo.toUInt16 ||| (hi.toUInt16 <<< 8)

/-- Read a little-endian 32-bit unsigned. -/
def u32le : Parser UInt32 := do
  let lo ← u16le; let hi ← u16le
  return lo.toUInt32 ||| (hi.toUInt32 <<< 16)

/-- Read a little-endian 64-bit unsigned. -/
def u64le : Parser UInt64 := do
  let lo ← u32le; let hi ← u32le
  return lo.toUInt64 ||| (hi.toUInt64 <<< 32)

/-- Read an exact byte sequence; fail if any byte mismatches. -/
def expect (expected : Array UInt8) : Parser Unit := do
  for byte in expected do
    let actual ← u8
    if actual != byte then throw s!"expect: got {actual}, want {byte}"

-- ============================================================================
-- BytesDecode typeclass
-- ============================================================================

/-- Type-driven byte decode. Per-struct instances are auto-derived
    by `deriving BytesDecode` (handler in `Parse/Deriving.lean`). -/
class BytesDecode (α : Type) where decode : Parser α

instance : BytesDecode UInt8  := ⟨u8⟩
instance : BytesDecode UInt16 := ⟨u16le⟩
instance : BytesDecode UInt32 := ⟨u32le⟩
instance : BytesDecode UInt64 := ⟨u64le⟩

/-- `n` bytes of don't-care padding. The decoder skips; nothing is
    retained. Used as a struct field to consume layout padding. -/
structure Pad (n : Nat) where deriving Inhabited, Repr

instance (n : Nat) : BytesDecode (Pad n) := ⟨do skip n; return {}⟩

/-- A type-level literal byte sequence. The decoder verifies the
    bytes match `bs` exactly; failure raises a parse error. Used
    for structural magic-byte checks. -/
structure Magic (bs : List UInt8) where deriving Inhabited, Repr

instance (bs : List UInt8) : BytesDecode (Magic bs) :=
  ⟨do expect bs.toArray; return {}⟩

/-- Decode `count` consecutive `α`-entries starting at file offset
    `offset`, using the `BytesDecode α` instance for each. -/
def decodeArray (offset count : Nat) [BytesDecode α] : Parser (Array α) := do
  seek offset
  let mut entries : Array α := Array.mkEmpty count
  for _ in [:count] do
    entries := entries.push (← BytesDecode.decode)
  return entries

section Example
#guard (Parser.run (ByteArray.mk #[0x12]) u8).toOption == some 0x12
#guard (Parser.run (ByteArray.mk #[0x34, 0x12]) u16le).toOption == some 0x1234
#guard (Parser.run (ByteArray.mk #[0x78, 0x56, 0x34, 0x12]) u32le).toOption == some 0x12345678
end Example

end LeanLoad.Parse

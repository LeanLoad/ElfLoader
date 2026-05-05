/-
Parser monad and byte-reader primitives.

The parser is `StateT State (Except String)`: a stateful read cursor over a
`ByteArray` that may fail with a string error. Every primitive bumps the
cursor by exactly the bytes it consumes.

Endianness is fixed to little-endian (LeanLoad targets x86-64 ELF64; gabi 02
§ ELF Identification rejects mixed-endian).
-/

namespace LeanLoad.Parse

/-- Parse state: source bytes plus current cursor offset. -/
structure State where
  bytes : ByteArray
  pos   : Nat

/-- Parser monad: stateful reads over a `ByteArray`, may fail with a message. -/
abbrev Parser (α : Type) : Type := StateT State (Except String) α

namespace Parser

/-- Run a parser starting at offset 0. -/
def run (b : ByteArray) (p : Parser α) : Except String α :=
  Prod.fst <$> StateT.run p ({ bytes := b, pos := 0 } : State)

/-- Run a parser starting at a given offset. -/
def runAt (b : ByteArray) (off : Nat) (p : Parser α) : Except String α :=
  Prod.fst <$> StateT.run p ({ bytes := b, pos := off } : State)

end Parser

namespace Bytes

/-- Current cursor offset. -/
def pos : Parser Nat := return (← get).pos

/-- Move the cursor to an absolute offset. Does not read. -/
def seek (off : Nat) : Parser Unit :=
  modify ({ · with pos := off })

/-- Skip `n` bytes from the current position. -/
def skip (n : Nat) : Parser Unit :=
  modify (fun s => { s with pos := s.pos + n })

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
  let lo ← u8
  let hi ← u8
  return lo.toUInt16 ||| (hi.toUInt16 <<< 8)

/-- Read a little-endian 32-bit unsigned. -/
def u32le : Parser UInt32 := do
  let lo ← u16le
  let hi ← u16le
  return lo.toUInt32 ||| (hi.toUInt32 <<< 16)

/-- Read a little-endian 64-bit unsigned. -/
def u64le : Parser UInt64 := do
  let lo ← u32le
  let hi ← u32le
  return lo.toUInt64 ||| (hi.toUInt64 <<< 32)

/-- Read `n` bytes as a sub-array. -/
def slice (n : Nat) : Parser ByteArray := do
  let s ← get
  if s.pos + n > s.bytes.size then
    throw s!"slice: out of bounds at {s.pos}+{n} (size {s.bytes.size})"
  set { s with pos := s.pos + n }
  return s.bytes.extract s.pos (s.pos + n)

/-- Read an exact byte sequence; fail if any byte mismatches. -/
def expect (expected : Array UInt8) : Parser Unit := do
  for byte in expected do
    let actual ← u8
    if actual != byte then
      throw s!"expect: got {actual}, want {byte}"

/-- Run `p` at an absolute offset, leaving the outer cursor unchanged. -/
def atOffset (off : Nat) (p : Parser α) : Parser α := do
  let saved ← pos
  seek off
  let v ← p
  seek saved
  return v

/-- Parse `count` consecutive entries with `p`, starting at `offset`. -/
def parseArray (offset count : Nat) (p : Parser α) : Parser (Array α) := do
  seek offset
  let mut entries : Array α := Array.mkEmpty count
  for _ in [:count] do
    entries := entries.push (← p)
  return entries

end Bytes

-- ============================================================================
-- Inline sanity: round-trip primitives over hand-crafted inputs.
-- ============================================================================

#guard (Parser.run (ByteArray.mk #[0x12]) Bytes.u8).toOption == some 0x12
#guard (Parser.run (ByteArray.mk #[0x34, 0x12]) Bytes.u16le).toOption == some 0x1234
#guard (Parser.run (ByteArray.mk #[0x78, 0x56, 0x34, 0x12]) Bytes.u32le).toOption == some 0x12345678

end LeanLoad.Parse

/-
Root scalar types and generic checked-constructor helpers.

Keep this module parse- and runtime-independent: later stages can import these
units without depending on ELF decoding or file IO.
-/

namespace LeanLoad

/-- Byte length / extent of a file or memory region. -/
structure ByteSize where
  val : UInt64
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

instance : OfNat ByteSize n where ofNat := ⟨n.toUInt64⟩

namespace ByteSize

def toNat (s : ByteSize) : Nat := s.val.toNat

/-- Convert arithmetic over `Nat` counts into a byte extent. -/
def ofNat (n : Nat) : ByteSize := ⟨n.toUInt64⟩

/-- Byte extent for `count` fixed-width entries. -/
def ofEntries (count : Nat) (entrySize : ByteSize) : ByteSize :=
  ofNat (count * entrySize.toNat)

end ByteSize

/-- Byte offset in an ELF file. -/
structure FileOff where
  val : UInt64
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

instance : OfNat FileOff n where ofNat := ⟨n.toUInt64⟩

namespace FileOff

def toNat (o : FileOff) : Nat := o.val.toNat

end FileOff

/-- ELF address from file metadata (`p_vaddr`, `.dynamic` pointers,
    relocation offsets). Distinct from file offsets and concrete mapped memory
    addresses. -/
structure Eaddr where
  val : UInt64
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

instance : OfNat Eaddr n where ofNat := ⟨n.toUInt64⟩

namespace Eaddr

def toNat (v : Eaddr) : Nat := v.val.toNat

end Eaddr

/-- Require a decidable proposition, preserving its proof on success. `PLift`
    bridges `Prop` through `Except`'s `Type` parameter. -/
def require (p : Prop) [Decidable p] (msg : String) : Except String (PLift p) :=
  if h : p then .ok ⟨h⟩ else .error msg

end LeanLoad

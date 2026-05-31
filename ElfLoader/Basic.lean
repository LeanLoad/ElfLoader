/-
Root scalar types and generic checked-constructor helpers.

Keep this module parse- and runtime-independent: later stages can import these
units without depending on ELF decoding or file IO.
-/

universe u v

namespace ElfLoader

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

/-- Build a dependent function over all `Fin n` indices, failing if any index's
    entry construction fails. Used by stages that validate every finite slot once
    and then expose total lookup functions at their boundary. -/
def buildFinFunction {ε : Type u} : {n : Nat} → {β : Fin n → Type v} →
    ((i : Fin n) → Except ε (β i)) →
    Except ε ((i : Fin n) → β i)
  | 0, _, _ => .ok (fun i => Fin.elim0 i)
  | n + 1, β, step => do
      let head ← step 0
      let tail ← buildFinFunction (ε := ε) (n := n) (β := fun i => β i.succ) fun i =>
        step i.succ
      return Fin.cases head tail

end ElfLoader

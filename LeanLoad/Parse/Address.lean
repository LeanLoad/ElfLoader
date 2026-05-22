import LeanLoad.Parse.Decode

/-!
Parse-stage address, offset, and extent types.

These names are deliberately owned by `Parse`: they describe coordinates and
byte extents as they appear in ELF metadata before later stages choose load
bases or concrete process addresses.
-/

namespace LeanLoad.Parse

/-- ELF address from file metadata (`p_vaddr`, `.dynamic` pointers,
    relocation offsets). Distinct from file offsets and concrete mapped memory
    addresses. -/
structure Eaddr where
  val : UInt64
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

instance : OfNat Eaddr n where ofNat := ⟨n.toUInt64⟩

def Eaddr.toNat (v : Eaddr) : Nat := v.val.toNat

/-- Byte offset in the ELF file. -/
structure FileOff where
  val : UInt64
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

instance : OfNat FileOff n where ofNat := ⟨n.toUInt64⟩

def FileOff.toNat (o : FileOff) : Nat := o.val.toNat

/-- Byte length / extent of a file or memory region. -/
structure ByteSize where
  val : UInt64
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

instance : OfNat ByteSize n where ofNat := ⟨n.toUInt64⟩

def ByteSize.toNat (s : ByteSize) : Nat := s.val.toNat

/-- ELF-address range `[start, start + size)` after dynamic-table semantics have
    interpreted the raw address payload as an ELF virtual-address coordinate.
    File-backed containment is added later by `RawElf.ImageView`. -/
structure EaddrRange where
  start : Eaddr
  size  : ByteSize
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

/-- Convert arithmetic over `Nat` counts into a byte extent. -/
def ByteSize.ofNat (n : Nat) : ByteSize := ⟨n.toUInt64⟩

/-- Byte extent for `count` fixed-width entries. -/
def ByteSize.ofEntries (count entrySize : Nat) : ByteSize :=
  ByteSize.ofNat (count * entrySize)

/-- Effective segment layout alignment: gabi 07 § Program Header permits
    `p_align = 0`; LeanLoad's total page math treats it as alignment 1. -/
def segmentLayoutAlign (align : UInt64) : UInt64 :=
  if align == 0 then 1 else align

/-- Half-open file-byte range `[off, off + len)` known to fit inside a file of
    observed byte size `fileSize`. This strengthens `(FileOff, ByteSize)`
    without making raw `FileOff` depend on a particular file. -/
structure FileRange (fileSize : UInt64) (off : FileOff) (len : ByteSize) where
  inFile : off.toNat + len.toNat ≤ fileSize.toNat

instance : RawDecode Eaddr UInt64 where ofRaw v := .ok ⟨v⟩
instance : RawDecode FileOff UInt64 where ofRaw v := .ok ⟨v⟩
instance : RawDecode ByteSize UInt64 where ofRaw v := .ok ⟨v⟩

/-- Byte offset into the dynamic string table (`.dynstr`). Consumed by
    `Strtab.lookup` to recover the NUL-terminated name at that
    offset. Distinct from `Eaddr` and `FileOff`. -/
structure StrtabOff where
  val : UInt64
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

instance : OfNat StrtabOff n where ofNat := ⟨n.toUInt64⟩

def StrtabOff.toNat (s : StrtabOff) : Nat := s.val.toNat

end LeanLoad.Parse

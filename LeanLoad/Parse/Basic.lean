import LeanLoad.Basic
import LeanLoad.Parse.Decode.Decodable

/-!
Parse-stage address types.

These names are deliberately owned by `Parse`: they describe parse-local
address ranges and offsets used while turning ELF bytes into checked parse-stage
data. Cross-stage scalar coordinates, byte extents, file offsets, and
proof-preserving checks live in `LeanLoad.Basic`.
-/

namespace LeanLoad.Parse

/-- ELF-address range `[start, start + size)` after dynamic-table semantics have
    interpreted the raw address payload as an ELF virtual-address coordinate.
    File-backed containment is added later by `LoadMap`. -/
structure EaddrRange where
  start : Eaddr
  size  : ByteSize
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

/-- Effective segment layout alignment: gabi 07 § Program Header permits
    `p_align = 0`; LeanLoad's total page math treats it as alignment 1. -/
def segmentLayoutAlign (align : UInt64) : UInt64 :=
  if align == 0 then 1 else align

instance : DecodableFromScalar Eaddr UInt64 where fromScalar v := .ok ⟨v⟩
instance : DecodableFromScalar FileOff UInt64 where fromScalar v := .ok ⟨v⟩
instance : DecodableFromScalar ByteSize UInt64 where fromScalar v := .ok ⟨v⟩

/-- Byte offset into the dynamic string table (`.dynstr`). Consumed by
    `Strtab.lookup` to recover the NUL-terminated name at that
    offset. Distinct from `Eaddr` and `FileOff`. -/
structure StrtabOff where
  val : UInt64
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

instance : OfNat StrtabOff n where ofNat := ⟨n.toUInt64⟩

def StrtabOff.toNat (s : StrtabOff) : Nat := s.val.toNat

end LeanLoad.Parse

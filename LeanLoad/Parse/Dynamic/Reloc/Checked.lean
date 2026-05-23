/-
Checked dynamic relocations.

`RawRela` is the byte-decoded relocation entry. `Rela` adds the segment-local
fact needed by planning and materialization: the relocation's conservative
8-byte write window is contained in the target segment's memory image.
-/

import LeanLoad.Parse.Dynamic.Reloc.Raw

namespace LeanLoad.Parse

/-- The segment's memory range fully contains an 8-byte write window starting
    at `r_offset`. Conservatively reserves 8 bytes. -/
def coversRela (eaddr : Eaddr) (memsz : ByteSize) (r_offset : Eaddr) : Prop :=
  eaddr.toNat ≤ r_offset.toNat ∧
  r_offset.toNat + 8 ≤ eaddr.toNat + memsz.toNat

instance (eaddr : Eaddr) (memsz : ByteSize) (r_offset : Eaddr) :
    Decidable (coversRela eaddr memsz r_offset) := by
  unfold coversRela; infer_instance

/-- A checked relocation whose 8-byte write window is contained in the segment
    range `[eaddr, eaddr + memsz)`. -/
structure Rela (eaddr : Eaddr) (memsz : ByteSize) where
  raw     : RawRela
  covered : coversRela eaddr memsz raw.r_offset
  deriving Repr

end LeanLoad.Parse

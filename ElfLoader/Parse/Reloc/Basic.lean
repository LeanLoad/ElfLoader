/-
Checked dynamic relocations.

`RawRela` is the byte-decoded relocation entry. `Reloc` adds the segment-local
fact needed by planning and materialization: the relocation's conservative
8-byte write window is contained in the target segment's memory image.
-/

import ElfLoader.Parse.Reloc.Raw
import ElfLoader.Parse.LoadMap.Segment.Basic

namespace ElfLoader.Parse

/-- A checked relocation whose 8-byte write window is contained in `segment`.
    The segment parameter records exactly which checked PT_LOAD owns the
    relocation, not just the anonymous address range. -/
structure Reloc {fileSize : ByteSize} (segment : Segment fileSize) where
  raw     : RawRela
  /-- The segment's memory range fully contains an 8-byte write window starting
      at `raw.r_offset`. Conservatively reserves 8 bytes. -/
  covered : segment.eaddr.toNat ≤ raw.r_offset.toNat ∧
    raw.r_offset.toNat + 8 ≤ segment.eaddr.toNat + segment.memsz.toNat
  deriving Repr

end ElfLoader.Parse

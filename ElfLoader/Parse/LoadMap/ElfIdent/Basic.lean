/-
ELF identification prefix (`e_ident`).
-/

import ElfLoader.Parse.Decode.Deriving
import ElfLoader.Parse.LoadMap.ElfIdent.Fields

namespace ElfLoader.Parse

/-- The 16-byte `e_ident` prefix of an ELF header.

    The padding bytes are retained as bytes but intentionally unchecked: gABI
    reserves them and says they should be zero, but they are not load-bearing
    for ElfLoader. -/
structure ElfIdent where
  magic         : IdentMagic
  ei_class      : IdentClass
  ei_data       : IdentData
  ei_version    : IdentVersion
  ei_osabi      : IdentOSABI
  ei_abiversion : IdentABIVersion
  pad0          : UInt8
  pad1          : UInt8
  pad2          : UInt8
  pad3          : UInt8
  pad4          : UInt8
  pad5          : UInt8
  pad6          : UInt8
  deriving Repr, Decodable

end ElfLoader.Parse

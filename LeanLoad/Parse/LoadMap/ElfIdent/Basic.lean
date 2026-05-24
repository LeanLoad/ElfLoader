/-
ELF identification prefix (`e_ident`).
-/

import LeanLoad.Parse.Decode.Deriving
import LeanLoad.Parse.LoadMap.ElfIdent.Fields

namespace LeanLoad.Parse

/-- The 16-byte `e_ident` prefix of an ELF header.

    The padding bytes are retained as bytes but intentionally unchecked: gABI
    reserves them and says they should be zero, but they are not load-bearing
    for LeanLoad. -/
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

end LeanLoad.Parse

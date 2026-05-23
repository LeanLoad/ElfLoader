/-
gabi 02 § ELF Header — `Elf64_Ehdr`. Field layout matches the C
struct one-for-one, including the inlined 16-byte `e_ident` prefix
(gabi 02 § ELF Identification).

The identification fields are typed in `Parse/FileView/ElfHeader/Ident.lean`; the
remaining header tag/version/sentinel fields are typed in
`Parse/FileView/ElfHeader/Fields.lean`. Their decoders fold validation and sentinel
decoding into byte decode, so later stages consume semantic fields
rather than raw integers.
-/

import LeanLoad.Parse.Decode
import LeanLoad.Parse.Deriving
import LeanLoad.Parse.Address
import LeanLoad.Parse.FileView.ElfHeader.Ident
import LeanLoad.Parse.FileView.ElfHeader.Fields
import LeanLoad.Parse.FileView.ProgramHeader.Basic

namespace LeanLoad.Parse

/-- 64-bit ELF file header. Field layout matches `Elf64_Ehdr` —
    the 16-byte `e_ident` is inlined as the first 7 fields (gabi 02
    declares `e_ident` as an `unsigned char[EI_NIDENT]`, not as a
    named sub-struct), followed by the remaining 48 bytes.

    Magic verification happens at decode time via the `Magic` field
    type: a wrong first byte short-circuits the entire `RawElfHeader`
    decode before any other field is read.

    Header tags/versions/sentinels are decoded through their semantic
    field types; unknown closed tags fail parsing. -/
structure RawElfHeader where
  -- ── e_ident (16 bytes, gabi 02 § ELF Identification) ─────────────────
  magic         : Magic [0x7f, 0x45, 0x4c, 0x46]
  ei_class      : IdentClass
  ei_data       : IdentData
  ei_version    : IdentVersion
  ei_osabi      : IdentOSABI
  ei_abiversion : IdentABIVersion
  _pad          : Pad 7
  -- ── rest of Elf64_Ehdr (48 bytes) ────────────────────────────────────
  e_type      : ElfType
  e_machine   : ElfMachine
  e_version   : ElfVersion
  e_entry     : Eaddr
  e_phoff     : FileOff
  e_shoff     : FileOff
  e_flags     : UInt32
  e_ehsize    : UInt16
  e_phentsize : UInt16
  e_phnum     : UInt16
  e_shentsize : UInt16
  e_shnum     : UInt16
  e_shstrndx  : ElfShstrndx
  deriving Repr, Inhabited, BytesDecode

/-- Size of `Elf64_Ehdr` on disk: 16-byte e_ident + 48 bytes = 64. -/
def ElfHeaderSize : Nat := 64

/-- ELF header accepted by LeanLoad's file-view stage. This wraps the decoded
    `RawElfHeader` with the policy and fixed-size facts the rest of the loader
    relies on. -/
structure ElfHeader extends RawElfHeader where
  class64     : ei_class = .class64
  littleEndian : ei_data = .lsb
  ehsizeOk    : e_ehsize.toNat = ElfHeaderSize
  phentsizeOk : e_phentsize.toNat = ProgramHeaderSize
  notExec     : e_type ≠ .exec
  deriving Repr

namespace ElfHeader

instance : Inhabited ElfHeader where
  default :=
    { toRawElfHeader := { (default : RawElfHeader) with
        ei_class := .class64,
        ei_data := .lsb,
        e_type := .dyn,
        e_ehsize := 64,
        e_phentsize := 56 },
      class64 := rfl,
      littleEndian := rfl,
      ehsizeOk := by decide,
      phentsizeOk := by decide,
      notExec := by decide }

/-- Lift a decidable header-policy proposition into `Except`, preserving the
   proof for the checked `ElfHeader` fields. -/
private def requirePolicy (p : Prop) [Decidable p] (msg : String) :
    Except String (PLift p) :=
  if h : p then .ok ⟨h⟩ else .error msg

/-- Attach LeanLoad's header policy and fixed record-size witnesses. -/
def ofRaw (header : RawElfHeader) : Except String ElfHeader := do
  let ⟨class64⟩ ← requirePolicy (header.ei_class = .class64)
    s!"parse: only ELFCLASS64 supported (got ei_class={reprStr header.ei_class})"
  let ⟨littleEndian⟩ ← requirePolicy (header.ei_data = .lsb)
    s!"parse: only little-endian supported (got ei_data={reprStr header.ei_data})"
  let ⟨ehsizeOk⟩ ← requirePolicy (header.e_ehsize.toNat = ElfHeaderSize)
    s!"parse: e_ehsize={header.e_ehsize} but Elf64_Ehdr is \
      {ElfHeaderSize} bytes (gabi-02 § ELF Header)"
  let ⟨phentsizeOk⟩ ← requirePolicy (header.e_phentsize.toNat = ProgramHeaderSize)
    s!"parse: e_phentsize={header.e_phentsize} but Elf64_Phdr is \
      {ProgramHeaderSize} bytes (gabi-07 § Program Header)"
  let ⟨notExec⟩ ← requirePolicy (header.e_type ≠ .exec)
    "parse: ET_EXEC not supported — LeanLoad expects PIE \
      (ET_DYN) inputs only. Recompile with -fPIE -pie."
  return {
    toRawElfHeader := header,
    class64,
    littleEndian,
    ehsizeOk,
    phentsizeOk,
    notExec
  }

/-- Decode and check one ELF header from the current cursor. -/
def parse : Decoder ElfHeader := do
  let raw : RawElfHeader ← BytesDecode.decode
  match ofRaw raw with
  | .ok header => return header
  | .error e   => throw e

end ElfHeader

end LeanLoad.Parse

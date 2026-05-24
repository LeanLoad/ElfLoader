/-
Typed ELF identification (`e_ident`) fields for `ElfHeader`.

Each typed field has a `DecodableFromScalar` from its on-disk scalar. Closed tables
fail on unknown codes during byte decode; open ranges preserve raw
values that LeanLoad does not currently interpret.

Spec: `third_party/gabi/docsrc/elf/02-eheader.rst`.
-/

import LeanLoad.Parse.Decode.Decodable

namespace LeanLoad.Parse

-- ELF identification: magic / `EI_CLASS` / `EI_DATA`
-- (gabi 02 § ELF Identification).

/-- ELF magic word, decoded from the first four bytes as little-endian
    `0x464c457f` (`0x7f 'E' 'L' 'F'`). -/
inductive IdentMagic where
  | elf
  deriving Repr, BEq, DecidableEq, Inhabited

instance : DecodableFromScalar IdentMagic UInt32 where
  fromScalar
  | 0x464c457f => .ok .elf
  | n => .error s!"EI_MAG: expected 0x464c457f, got {n.toNat}"

/-- `EI_CLASS`: 32-bit vs 64-bit object format. -/
inductive IdentClass where
  | class32
  | class64
  deriving Repr, BEq, DecidableEq, Inhabited

instance : DecodableFromScalar IdentClass UInt8 where
  fromScalar
  | 1 => .ok .class32
  | 2 => .ok .class64
  | n => .error s!"EI_CLASS: unknown value {n} (gabi 02 § ELF Identification)"

/-- `EI_DATA`: byte order used by multi-byte fields. -/
inductive IdentData where
  | lsb
  | msb
  deriving Repr, BEq, DecidableEq, Inhabited

instance : DecodableFromScalar IdentData UInt8 where
  fromScalar
  | 1 => .ok .lsb
  | 2 => .ok .msb
  | n => .error s!"EI_DATA: unknown value {n} (gabi 02 § ELF Identification)"

-- ELF identification version: `EI_VERSION` (gabi 02 § ELF Identification).
-- `EV_NONE = 0` is named but invalid; currently-valid objects carry `EV_CURRENT = 1`.

/-- `EI_VERSION`: ELF identification version. -/
inductive IdentVersion where
  | current
  deriving Repr, BEq, DecidableEq, Inhabited

instance : DecodableFromScalar IdentVersion UInt8 where
  fromScalar
  | 1 => .ok .current -- EV_CURRENT (gabi 02 § ELF Identification)
  | n => .error s!"EI_VERSION: expected EV_CURRENT=1, got {n} (gabi 02 § ELF Identification)"

/-- `EI_ABIVERSION`: OS/ABI-specific ABI version byte. -/
structure IdentABIVersion where
  value : UInt8
  deriving Repr, BEq, DecidableEq, Inhabited

instance : DecodableFromScalar IdentABIVersion UInt8 where
  fromScalar n := .ok ⟨n⟩

-- Operating system / ABI selector: `EI_OSABI` (gabi Appendix B and
-- gabi 02 § ELF Identification). Values `64..255` are arch/psABI-
-- specific; unassigned generic values remain representable so the
-- raw header preserves bytes LeanLoad does not currently interpret.

/-- `EI_OSABI`: generic gABI assignments plus raw generic/arch-specific values. -/
inductive IdentOSABI where
  | none
  | hpux
  | netbsd
  | gnu
  | solaris
  | aix
  | irix
  | freebsd
  | tru64
  | modesto
  | openbsd
  | openvms
  | nsk
  | aros
  | fenixos
  | cloudabi
  | openvos
  | generic (value : UInt8)
  | archSpecific (value : UInt8)
  deriving Repr, BEq, DecidableEq, Inhabited

instance : DecodableFromScalar IdentOSABI UInt8 where
  fromScalar
  | 0  => .ok .none       -- ELFOSABI_NONE (gabi Appendix B)
  | 1  => .ok .hpux       -- ELFOSABI_HPUX
  | 2  => .ok .netbsd     -- ELFOSABI_NETBSD
  | 3  => .ok .gnu        -- ELFOSABI_GNU / historical ELFOSABI_LINUX
  | 6  => .ok .solaris    -- ELFOSABI_SOLARIS
  | 7  => .ok .aix        -- ELFOSABI_AIX
  | 8  => .ok .irix       -- ELFOSABI_IRIX
  | 9  => .ok .freebsd    -- ELFOSABI_FREEBSD
  | 10 => .ok .tru64      -- ELFOSABI_TRU64
  | 11 => .ok .modesto    -- ELFOSABI_MODESTO
  | 12 => .ok .openbsd    -- ELFOSABI_OPENBSD
  | 13 => .ok .openvms    -- ELFOSABI_OPENVMS
  | 14 => .ok .nsk        -- ELFOSABI_NSK
  | 15 => .ok .aros       -- ELFOSABI_AROS
  | 16 => .ok .fenixos    -- ELFOSABI_FENIXOS
  | 17 => .ok .cloudabi   -- ELFOSABI_CLOUDABI
  | 18 => .ok .openvos    -- ELFOSABI_OPENVOS
  | n  =>
      if n < 64 then .ok (.generic n) else .ok (.archSpecific n)

end LeanLoad.Parse

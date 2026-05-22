/-
Typed `Elf64_Ehdr` tags and semantic scalar fields for `RawEhdr`.

Each typed field has a `ByteMap` from its on-disk integer code.
Closed tables fail on unknown codes during byte decode; open or
sentinel-carrying namespaces classify every raw value into a semantic
case. Loader policy such as "64-bit only" or "ET_DYN only" is enforced
later.

Spec: `third_party/gabi/docsrc/elf/02-eheader.rst`.
-/

import LeanLoad.Parse.Decode

namespace LeanLoad.Parse

-- ELF identification: `EI_CLASS` / `EI_DATA` (gabi 02 § ELF Identification).

/-- `EI_CLASS`: 32-bit vs 64-bit object format. -/
inductive ElfClass where
  | class32
  | class64
  deriving Repr, BEq, DecidableEq, Inhabited

instance : ByteMap ElfClass UInt8 where
  ofRaw
  | 1 => .ok .class32
  | 2 => .ok .class64
  | n => .error s!"EI_CLASS: unknown value {n} (gabi 02 § ELF Identification)"

/-- `EI_DATA`: byte order used by multi-byte fields. -/
inductive ElfData where
  | lsb
  | msb
  deriving Repr, BEq, DecidableEq, Inhabited

instance : ByteMap ElfData UInt8 where
  ofRaw
  | 1 => .ok .lsb
  | 2 => .ok .msb
  | n => .error s!"EI_DATA: unknown value {n} (gabi 02 § ELF Identification)"

-- ELF version fields: `EI_VERSION` and `e_version` (gabi 02 § ELF
-- Identification / § ELF Header). `EV_NONE = 0` is named but invalid;
-- currently-valid objects carry `EV_CURRENT = 1`.

/-- `EI_VERSION`: ELF identification version. -/
inductive ElfIdentVersion where
  | current
  deriving Repr, BEq, DecidableEq, Inhabited

instance : ByteMap ElfIdentVersion UInt8 where
  ofRaw
  | 1 => .ok .current -- EV_CURRENT (gabi 02 § ELF Identification)
  | n => .error s!"EI_VERSION: expected EV_CURRENT=1, got {n} (gabi 02 § ELF Identification)"

/-- `e_version`: ELF object file version. -/
inductive ElfFileVersion where
  | current
  deriving Repr, BEq, DecidableEq, Inhabited

instance : ByteMap ElfFileVersion UInt32 where
  ofRaw
  | 1 => .ok .current -- EV_CURRENT (gabi 02 § ELF Header)
  | n => .error s!"e_version: expected EV_CURRENT=1, got {n} (gabi 02 § ELF Header)"

-- Operating system / ABI selector: `EI_OSABI` (gabi Appendix B and
-- gabi 02 § ELF Identification). Values `64..255` are arch/psABI-
-- specific; unassigned generic values remain representable so the
-- raw header preserves bytes LeanLoad does not currently interpret.

/-- `EI_OSABI`: generic gABI assignments plus raw generic/arch-specific values. -/
inductive ElfOSABI where
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

instance : ByteMap ElfOSABI UInt8 where
  ofRaw
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

-- Object file type: `e_type` (gabi 02 § Object File Types).

/-- `e_type`: coarse ELF object category. -/
inductive ElfType where
  | none
  | rel
  | exec
  | dyn
  | core
  deriving Repr, BEq, DecidableEq, Inhabited

instance : ByteMap ElfType UInt16 where
  ofRaw
  | 0 => .ok .none
  | 1 => .ok .rel
  | 2 => .ok .exec
  | 3 => .ok .dyn
  | 4 => .ok .core
  | n => .error s!"e_type: unknown value {n} (gabi 02 § Object File Types)"

-- Target ISA / psABI: `e_machine` (gabi 02 § Machine, full list in
-- `third_party/gabi/docsrc/elf/a-emachine.rst`).

/-- `e_machine`: architectures with relocation tables in LeanLoad. -/
inductive ElfMachine where
  | x86_64
  | aarch64
  deriving Repr, BEq, DecidableEq, Inhabited

instance : ByteMap ElfMachine UInt16 where
  ofRaw
  | 62  => .ok .x86_64
  | 183 => .ok .aarch64
  | n   => .error s!"e_machine: unsupported value {n}; expected EM_X86_64=62 \
      or EM_AARCH64=183 (gabi 02 § Machine)"

-- Section-name string table index: `e_shstrndx` (gabi 02 § ELF
-- Header). `SHN_UNDEF = 0` means absent; `SHN_XINDEX = 0xffff` means
-- the actual index lives in section header 0's `sh_link`.

/-- `e_shstrndx`: section-name string table index or gABI sentinel. -/
inductive EhdrShstrndx where
  | undef
  | index (value : UInt16)
  | xindex
  deriving Repr, BEq, DecidableEq, Inhabited

instance : ByteMap EhdrShstrndx UInt16 where
  ofRaw
  | 0      => .ok .undef  -- SHN_UNDEF (gabi 02 § ELF Header)
  | 65535  => .ok .xindex -- SHN_XINDEX (gabi 02 § ELF Header)
  | n      => .ok (.index n)

end LeanLoad.Parse

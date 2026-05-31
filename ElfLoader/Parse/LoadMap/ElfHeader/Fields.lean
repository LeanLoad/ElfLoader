/-
Typed fields for `ElfHeader` outside `e_ident`.

Each typed field has a `DecodableFromScalar` from its on-disk integer code.
Closed tables fail on unknown codes during byte decode; sentinel-carrying
fields classify every raw value into a semantic case. Loader policy such
as "ET_DYN only" is enforced later.

Spec: `third_party/gabi/docsrc/elf/02-eheader.rst`.
-/

import ElfLoader.Parse.Decode.Decodable

namespace ElfLoader.Parse

/-- `e_version`: ELF object file version. -/
inductive ElfVersion where
  | current
  deriving Repr, BEq, DecidableEq, Inhabited

instance : DecodableFromScalar ElfVersion UInt32 where
  fromScalar
  | 1 => .ok .current -- EV_CURRENT (gabi 02 § ELF Header)
  | n => .error s!"e_version: expected EV_CURRENT=1, got {n} (gabi 02 § ELF Header)"

-- Object file type: `e_type` (gabi 02 § Object File Types).

/-- `e_type`: coarse ELF object category. -/
inductive ElfType where
  | none
  | rel
  | exec
  | dyn
  | core
  deriving Repr, BEq, DecidableEq, Inhabited

instance : DecodableFromScalar ElfType UInt16 where
  fromScalar
  | 0 => .ok .none
  | 1 => .ok .rel
  | 2 => .ok .exec
  | 3 => .ok .dyn
  | 4 => .ok .core
  | n => .error s!"e_type: unknown value {n} (gabi 02 § Object File Types)"

-- Target ISA / psABI: `e_machine` (gabi 02 § Machine, full list in
-- `third_party/gabi/docsrc/elf/a-emachine.rst`).

/-- `e_machine`: architectures with relocation tables in ElfLoader. -/
inductive ElfMachine where
  | x86_64
  | aarch64
  deriving Repr, BEq, DecidableEq, Inhabited

instance : DecodableFromScalar ElfMachine UInt16 where
  fromScalar
  | 62  => .ok .x86_64
  | 183 => .ok .aarch64
  | n   => .error s!"e_machine: unsupported value {n}; expected EM_X86_64=62 \
      or EM_AARCH64=183 (gabi 02 § Machine)"

-- Section-name string table index: `e_shstrndx` (gabi 02 § ELF
-- Header). `SHN_UNDEF = 0` means absent; `SHN_XINDEX = 0xffff` means
-- the actual index lives in section header 0's `sh_link`.

/-- `e_shstrndx`: section-name string table index or gABI sentinel. -/
inductive ElfShstrndx where
  | undef
  | index (value : UInt16)
  | xindex
  deriving Repr, BEq, DecidableEq, Inhabited

instance : DecodableFromScalar ElfShstrndx UInt16 where
  fromScalar
  | 0      => .ok .undef  -- SHN_UNDEF (gabi 02 § ELF Header)
  | 65535  => .ok .xindex -- SHN_XINDEX (gabi 02 § ELF Header)
  | n      => .ok (.index n)

end ElfLoader.Parse

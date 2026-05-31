/-
gabi 08 § Dynamic Section — typed field values for `Elf64_Dyn`.

Spec: gabi 08 (`third_party/gabi/docsrc/elf/08-dynamic.rst`) § Dynamic
Array Tags.

The generic gABI names are decoded to constructors. OS-specific and
processor-specific ranges stay representable as raw values, and other
unassigned values are classified as reserved.
-/

import ElfLoader.Parse.Decode.Decodable

namespace ElfLoader.Parse

/-- Dynamic-array tag (`d_tag`).

    gABI 08 § Dynamic Section defines named values, reserves
    `DT_LOOS..DT_HIOS` for OS-specific semantics, reserves
    `DT_LOPROC..DT_HIPROC` for processor-specific semantics, and leaves
    other unassigned values reserved. -/
inductive DynTag where
  | null
  | needed
  | pltrelsz
  | pltgot
  | hash
  | strtab
  | symtab
  | rela
  | relasz
  | relaent
  | strsz
  | syment
  | init
  | fini
  | soname
  | rpath
  | symbolic
  | rel
  | relsz
  | relent
  | pltrel
  | debug
  | textrel
  | jmprel
  | bindNow
  | initArray
  | finiArray
  | initArraySz
  | finiArraySz
  | runpath
  | flags
  | preinitArray
  | preinitArraySz
  | symtabShndx
  | osSpecific (raw : UInt64)
  | procSpecific (raw : UInt64)
  | reserved (raw : UInt64)
  deriving Repr, BEq, DecidableEq, Inhabited

instance : DecodableFromScalar DynTag UInt64 where
  fromScalar
  | 0  => .ok .null
  | 1  => .ok .needed
  | 2  => .ok .pltrelsz
  | 3  => .ok .pltgot
  | 4  => .ok .hash
  | 5  => .ok .strtab
  | 6  => .ok .symtab
  | 7  => .ok .rela
  | 8  => .ok .relasz
  | 9  => .ok .relaent
  | 10 => .ok .strsz
  | 11 => .ok .syment
  | 12 => .ok .init
  | 13 => .ok .fini
  | 14 => .ok .soname
  | 15 => .ok .rpath
  | 16 => .ok .symbolic
  | 17 => .ok .rel
  | 18 => .ok .relsz
  | 19 => .ok .relent
  | 20 => .ok .pltrel
  | 21 => .ok .debug
  | 22 => .ok .textrel
  | 23 => .ok .jmprel
  | 24 => .ok .bindNow
  | 25 => .ok .initArray
  | 26 => .ok .finiArray
  | 27 => .ok .initArraySz
  | 28 => .ok .finiArraySz
  | 29 => .ok .runpath
  | 30 => .ok .flags
  | 32 => .ok .preinitArray -- DT_ENCODING is the boundary marker at the same value.
  | 33 => .ok .preinitArraySz
  | 34 => .ok .symtabShndx
  | n  =>
      if 0x6000000d ≤ n.toNat ∧ n.toNat ≤ 0x6ffff000 then
        .ok (.osSpecific n)   -- DT_LOOS..DT_HIOS (gabi 08 § Dynamic Section)
      else if 0x70000000 ≤ n.toNat ∧ n.toNat ≤ 0x7fffffff then
        .ok (.procSpecific n) -- DT_LOPROC..DT_HIPROC (gabi 08 § Dynamic Section)
      else
        .ok (.reserved n)

namespace DynTag

/-- gABI spelling for diagnostics. Open OS/proc/reserved ranges keep their raw
    numeric value because there is no single standard tag name. -/
def label : DynTag → String
  | .null             => "DT_NULL"
  | .needed           => "DT_NEEDED"
  | .pltrelsz         => "DT_PLTRELSZ"
  | .pltgot           => "DT_PLTGOT"
  | .hash             => "DT_HASH"
  | .strtab           => "DT_STRTAB"
  | .symtab           => "DT_SYMTAB"
  | .rela             => "DT_RELA"
  | .relasz           => "DT_RELASZ"
  | .relaent          => "DT_RELAENT"
  | .strsz            => "DT_STRSZ"
  | .syment           => "DT_SYMENT"
  | .init             => "DT_INIT"
  | .fini             => "DT_FINI"
  | .soname           => "DT_SONAME"
  | .rpath            => "DT_RPATH"
  | .symbolic         => "DT_SYMBOLIC"
  | .rel              => "DT_REL"
  | .relsz            => "DT_RELSZ"
  | .relent           => "DT_RELENT"
  | .pltrel           => "DT_PLTREL"
  | .debug            => "DT_DEBUG"
  | .textrel          => "DT_TEXTREL"
  | .jmprel           => "DT_JMPREL"
  | .bindNow          => "DT_BIND_NOW"
  | .initArray        => "DT_INIT_ARRAY"
  | .finiArray        => "DT_FINI_ARRAY"
  | .initArraySz      => "DT_INIT_ARRAYSZ"
  | .finiArraySz      => "DT_FINI_ARRAYSZ"
  | .runpath          => "DT_RUNPATH"
  | .flags            => "DT_FLAGS"
  | .preinitArray     => "DT_PREINIT_ARRAY"
  | .preinitArraySz   => "DT_PREINIT_ARRAYSZ"
  | .symtabShndx      => "DT_SYMTAB_SHNDX"
  | .osSpecific raw   => s!"DT_OS_SPECIFIC({raw.toNat})"
  | .procSpecific raw => s!"DT_PROC_SPECIFIC({raw.toNat})"
  | .reserved raw     => s!"DT_RESERVED({raw.toNat})"

#guard DynTag.label .strtab = "DT_STRTAB"
#guard DynTag.label .relaent = "DT_RELAENT"

end DynTag

/-- Values stored in `DT_PLTREL.d_un`. gABI 08 § Dynamic Array Tags says the
    value is either `DT_REL` or `DT_RELA`; ElfLoader currently accepts only
    `.rela` because `DT_JMPREL` is decoded with `Elf64_Rela`. -/
inductive PltRelKind where
  | rel
  | rela
  deriving Repr, BEq, DecidableEq, Inhabited

namespace PltRelKind

/-- Decode a raw `DT_PLTREL` payload. Constants are gABI 08 § Dynamic
    Array Tags: `DT_RELA = 7`, `DT_REL = 17`. -/
def ofRaw : UInt64 → Except String PltRelKind
  | 7  => .ok .rela
  | 17 => .ok .rel
  | raw =>
      .error s!"parse: DT_PLTREL={raw.toNat}, expected DT_RELA (7) or DT_REL (17)"

#guard
  match PltRelKind.ofRaw 7 with
  | .ok .rela => true
  | _         => false

#guard
  match PltRelKind.ofRaw 17 with
  | .ok .rel => true
  | _        => false

#guard
  match PltRelKind.ofRaw 0 with
  | .ok _    => false
  | .error _ => true

end PltRelKind

end ElfLoader.Parse

/-
gabi 08 § Dynamic Section — typed field values for `Elf64_Dyn`.

Spec: gabi 08 (`third_party/gabi/docsrc/elf/08-dynamic.rst`) § Dynamic
Array Tags.

The generic gABI names are decoded to constructors. OS-specific and
processor-specific ranges stay representable as raw values, and other
unassigned values are classified as reserved.
-/

import LeanLoad.Parse.Decode

namespace LeanLoad.Parse

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

instance : RawDecode DynTag UInt64 where
  ofRaw
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

/-- Values stored in `DT_PLTREL.d_un`. gABI 08 § Dynamic Array Tags says the
    value is either `DT_REL` or `DT_RELA`; LeanLoad currently accepts only
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

end LeanLoad.Parse

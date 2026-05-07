/-
x86-64 relocation formulas.

Spec: x86-64 psABI § Relocation Types
(`third_party/x86-64-ABI/x86-64-ABI/object-files.tex`, table
`tab-relocations`). Subset for the loader-minimal scope (no TLS, no
`IFUNC`, no `COPY`):

| Type                  | Code | Width | Formula |
| --------------------- | ---- | ----- | ------- |
| `R_X86_64_NONE`       |    0 |   —   | none    |
| `R_X86_64_64`         |    1 |   8   | S + A   |
| `R_X86_64_GLOB_DAT`   |    6 |   8   | S       |
| `R_X86_64_JUMP_SLOT`  |    7 |   8   | S       |
| `R_X86_64_RELATIVE`   |    8 |   8   | B + A   |
| `R_X86_64_32`         |   10 |   4   | S + A   |

`GLOB_DAT` / `JUMP_SLOT` are `S` per the psABI table — no addend.
(AArch64 documents them as `S + A`; the addend is conventionally 0
in both cases, but we follow each arch's spec literally.)

`R_X86_64_32` truncates to 32 bits.
-/

import LeanLoad.Elaborate.Reloc

namespace LeanLoad.Elaborate.X86_64

open LeanLoad.Elaborate

def R_X86_64_NONE      : UInt32 := 0
def R_X86_64_64        : UInt32 := 1
def R_X86_64_GLOB_DAT  : UInt32 := 6
def R_X86_64_JUMP_SLOT : UInt32 := 7
def R_X86_64_RELATIVE  : UInt32 := 8
def R_X86_64_32        : UInt32 := 10

/-- Apply an x86-64 dynamic-relocation formula. Returns `none` for
    `R_X86_64_NONE` and any unsupported type. -/
def formula : Formula := fun ty inp =>
  let S := inp.symValue
  let A := inp.addend
  let B := inp.base
  if ty == R_X86_64_NONE       then none
  else if ty == R_X86_64_64        then some { value := S + A, size := .b8 }
  else if ty == R_X86_64_GLOB_DAT  then some { value := S,     size := .b8 }
  else if ty == R_X86_64_JUMP_SLOT then some { value := S,     size := .b8 }
  else if ty == R_X86_64_RELATIVE  then some { value := B + A, size := .b8 }
  else if ty == R_X86_64_32        then some { value := S + A, size := .b4 }
  else none

#guard (formula R_X86_64_NONE  { symValue := 0xdead, addend := 0xbeef, base := 0xcafe, place := 0xbabe }) == none
#guard (formula 999 { symValue := 0, addend := 0, base := 0, place := 0 }) == none

#guard (formula R_X86_64_RELATIVE { symValue := 0xdead, addend := 0xa90, base := 0x10000, place := 0 })
    == (formula R_X86_64_RELATIVE { symValue := 0xbeef, addend := 0xa90, base := 0x10000, place := 0 })
#guard (formula R_X86_64_RELATIVE { symValue := 0,      addend := 0xa90, base := 0x10000, place := 0 })
        == some { value := 0x10a90, size := .b8 }

#guard (formula R_X86_64_64 { symValue := 100, addend := 1, base := 0xdead, place := 0 })
    == (formula R_X86_64_64 { symValue := 100, addend := 1, base := 0xbeef, place := 0 })
#guard (formula R_X86_64_64 { symValue := 0xfeedface, addend := 0, base := 0, place := 0 })
        == some { value := 0xfeedface, size := .b8 }
#guard (formula R_X86_64_32 { symValue := 0xc0ffee,   addend := 0, base := 0, place := 0 })
        == some { value := 0xc0ffee,   size := .b4 }

#guard (formula R_X86_64_GLOB_DAT  { symValue := 0xdeadbeef, addend := 0xbad, base := 0, place := 0 })
        == some { value := 0xdeadbeef, size := .b8 }
#guard (formula R_X86_64_JUMP_SLOT { symValue := 0xb16b00b5, addend := 0xbad, base := 0, place := 0 })
        == some { value := 0xb16b00b5, size := .b8 }

#guard (formula R_X86_64_64 { symValue := 0xFFFFFFFFFFFFFFFF, addend := 1, base := 0, place := 0 })
        == some { value := 0, size := .b8 }

end LeanLoad.Elaborate.X86_64

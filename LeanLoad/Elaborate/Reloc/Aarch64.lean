/-
AArch64 relocation formulas.

Spec: ARM ELF for the AArch64 ABI § Dynamic Relocations. Subset
needed for the loader-minimal scope (no static-link relocations, no
TLS, no `IFUNC`):

| Type                  | Code | Width | Formula |
| --------------------- | ---- | ----- | ------- |
| `R_AARCH64_NONE`      |    0 |   —   | none    |
| `R_AARCH64_ABS64`     |  257 |   8   | S + A   |
| `R_AARCH64_ABS32`     |  258 |   4   | S + A   |
| `R_AARCH64_GLOB_DAT`  | 1025 |   8   | S + A   |
| `R_AARCH64_JUMP_SLOT` | 1026 |   8   | S + A   |
| `R_AARCH64_RELATIVE`  | 1027 |   8   | B + A   |

Note: `GLOB_DAT` and `JUMP_SLOT` are documented as `S + A` for
completeness; in practice the linker emits them with `A = 0`.
-/

import LeanLoad.Elaborate.Reloc

namespace LeanLoad.Elaborate.Aarch64

open LeanLoad.Elaborate

def R_AARCH64_NONE      : UInt32 := 0
def R_AARCH64_ABS64     : UInt32 := 257
def R_AARCH64_ABS32     : UInt32 := 258
def R_AARCH64_GLOB_DAT  : UInt32 := 1025
def R_AARCH64_JUMP_SLOT : UInt32 := 1026
def R_AARCH64_RELATIVE  : UInt32 := 1027

/-- Apply an AArch64 dynamic-relocation formula. Returns `none` for
    `R_AARCH64_NONE` and any unsupported type. -/
def formula : Formula := fun ty inp =>
  let S := inp.symValue
  let A := inp.addend
  let B := inp.base
  if ty == R_AARCH64_NONE      then none
  else if ty == R_AARCH64_ABS64     then some { value := S + A, size := .b8 }
  else if ty == R_AARCH64_ABS32     then some { value := S + A, size := .b4 }
  else if ty == R_AARCH64_GLOB_DAT  then some { value := S + A, size := .b8 }
  else if ty == R_AARCH64_JUMP_SLOT then some { value := S + A, size := .b8 }
  else if ty == R_AARCH64_RELATIVE  then some { value := B + A, size := .b8 }
  else none

#guard (formula R_AARCH64_NONE      { symValue := 0xdead, addend := 0xbeef, base := 0xcafe, place := 0xbabe }) == none
#guard (formula 999 { symValue := 0, addend := 0, base := 0, place := 0 }) == none

#guard (formula R_AARCH64_RELATIVE { symValue := 0xdead, addend := 0xa90, base := 0x10000, place := 0 })
    == (formula R_AARCH64_RELATIVE { symValue := 0xbeef, addend := 0xa90, base := 0x10000, place := 0 })
#guard (formula R_AARCH64_RELATIVE { symValue := 0,      addend := 0xa90, base := 0x10000, place := 0 })
        == some { value := 0x10a90, size := .b8 }

#guard (formula R_AARCH64_ABS64 { symValue := 100, addend := 1, base := 0xdead, place := 0 })
    == (formula R_AARCH64_ABS64 { symValue := 100, addend := 1, base := 0xbeef, place := 0 })
#guard (formula R_AARCH64_ABS64    { symValue := 0xfeedface, addend := 0, base := 0, place := 0 })
        == some { value := 0xfeedface, size := .b8 }
#guard (formula R_AARCH64_ABS32    { symValue := 0xc0ffee,   addend := 0, base := 0, place := 0 })
        == some { value := 0xc0ffee,   size := .b4 }

#guard (formula R_AARCH64_GLOB_DAT  { symValue := 0xdeadbeef, addend := 0, base := 0, place := 0 })
        == some { value := 0xdeadbeef, size := .b8 }
#guard (formula R_AARCH64_JUMP_SLOT { symValue := 0xb16b00b5, addend := 0, base := 0, place := 0 })
        == some { value := 0xb16b00b5, size := .b8 }

#guard (formula R_AARCH64_ABS64 { symValue := 0xFFFFFFFFFFFFFFFF, addend := 1, base := 0, place := 0 })
        == some { value := 0, size := .b8 }

end LeanLoad.Elaborate.Aarch64

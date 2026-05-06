/-
x86-64 relocation formulas.

Spec: x86-64 psABI § Relocation Types
(`third_party/x86-64-ABI/x86-64-ABI/object-files.tex`, table
`tab-relocations`). Subset needed for the loader-minimal scope (no
TLS, no `IFUNC`, no `COPY` since the `Formula` type can't model
"copy bytes from another object's symbol"):

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

`R_X86_64_32` truncates to 32 bits. The psABI also asks the linker
to verify that the value zero-extends to the original 64-bit value;
that overflow check is not modelled here.
-/

import LeanLoad.Reloc

namespace LeanLoad.Spec.Reloc.X86_64

open LeanLoad.Reloc

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
  else if ty == R_X86_64_64        then some { value := S + A, size := 8 }
  else if ty == R_X86_64_GLOB_DAT  then some { value := S,     size := 8 }
  else if ty == R_X86_64_JUMP_SLOT then some { value := S,     size := 8 }
  else if ty == R_X86_64_RELATIVE  then some { value := B + A, size := 8 }
  else if ty == R_X86_64_32        then some { value := S + A, size := 4 }
  else none

-- Compile-time unit tests. Evaluated at elaboration; a wrong table
-- fails to build. Totality is proved in `LeanLoad.Thm`.

#guard (formula R_X86_64_NONE  { symValue := 0xdead, addend := 0xbeef, base := 0xcafe, place := 0xbabe }) == none
#guard (formula 999 { symValue := 0, addend := 0, base := 0, place := 0 }) == none

-- RELATIVE = B + A: only base+addend matter.
#guard (formula R_X86_64_RELATIVE { symValue := 0xdead, addend := 0xa90, base := 0x10000, place := 0 })
    == (formula R_X86_64_RELATIVE { symValue := 0xbeef, addend := 0xa90, base := 0x10000, place := 0 })
#guard (formula R_X86_64_RELATIVE { symValue := 0,      addend := 0xa90, base := 0x10000, place := 0 })
        == some { value := 0x10a90, size := 8 }

-- 64 = S + A. base/place unused.
#guard (formula R_X86_64_64 { symValue := 100, addend := 1, base := 0xdead, place := 0 })
    == (formula R_X86_64_64 { symValue := 100, addend := 1, base := 0xbeef, place := 0 })
#guard (formula R_X86_64_64 { symValue := 0xfeedface, addend := 0, base := 0, place := 0 })
        == some { value := 0xfeedface, size := 8 }
#guard (formula R_X86_64_32 { symValue := 0xc0ffee,   addend := 0, base := 0, place := 0 })
        == some { value := 0xc0ffee,   size := 4 }

-- GLOB_DAT / JUMP_SLOT = S (no addend per psABI).
#guard (formula R_X86_64_GLOB_DAT  { symValue := 0xdeadbeef, addend := 0xbad, base := 0, place := 0 })
        == some { value := 0xdeadbeef, size := 8 }
#guard (formula R_X86_64_JUMP_SLOT { symValue := 0xb16b00b5, addend := 0xbad, base := 0, place := 0 })
        == some { value := 0xb16b00b5, size := 8 }

-- UInt64 wraps modulo 2^64.
#guard (formula R_X86_64_64 { symValue := 0xFFFFFFFFFFFFFFFF, addend := 1, base := 0, place := 0 })
        == some { value := 0, size := 8 }

-- Planner-on-this-formula canary: one R_X86_64_RELATIVE rela → one write.
section UnitTest
open LeanLoad.Test

private def relocLM : LeanLoad.Discover.LinkMap := {
  objects := #[synthObj "main"
    (rela := #[{
      r_offset := 0x1000
      r_info   := 8      -- R_X86_64_RELATIVE = type only, symIdx = 0
      r_addend := 0xa90
    }])]
}

#guard (plan formula relocLM #[0x10000]
          (Resolve.buildTable relocLM)).size = 1

end UnitTest

end LeanLoad.Spec.Reloc.X86_64

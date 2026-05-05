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

import LeanLoad.Plan.Reloc
import LeanLoad.TestFixture

namespace LeanLoad.Plan.Reloc.Aarch64

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
  else if ty == R_AARCH64_ABS64     then some { value := S + A, size := 8 }
  else if ty == R_AARCH64_ABS32     then some { value := S + A, size := 4 }
  else if ty == R_AARCH64_GLOB_DAT  then some { value := S + A, size := 8 }
  else if ty == R_AARCH64_JUMP_SLOT then some { value := S + A, size := 8 }
  else if ty == R_AARCH64_RELATIVE  then some { value := B + A, size := 8 }
  else none

-- Compile-time unit tests. Evaluated at elaboration, so a wrong table
-- fails to build. Totality is proved in `LeanLoad.Thm`; here we
-- exercise behavioural properties.

-- A skipped reloc is not a zero write — "no operation" is structural.
#guard (formula R_AARCH64_NONE      { symValue := 0xdead, addend := 0xbeef, base := 0xcafe, place := 0xbabe }) == none

-- An unknown type also yields none (totality boundary).
#guard (formula 999 { symValue := 0, addend := 0, base := 0, place := 0 }) == none

-- RELATIVE = B + A. By construction, *only* base and addend matter:
-- swapping symValue must not perturb the result.
#guard (formula R_AARCH64_RELATIVE { symValue := 0xdead, addend := 0xa90, base := 0x10000, place := 0 })
    == (formula R_AARCH64_RELATIVE { symValue := 0xbeef, addend := 0xa90, base := 0x10000, place := 0 })
#guard (formula R_AARCH64_RELATIVE { symValue := 0,      addend := 0xa90, base := 0x10000, place := 0 })
        == some { value := 0x10a90, size := 8 }

-- ABS-family = S + A. Symmetrically, base and place are unused.
#guard (formula R_AARCH64_ABS64 { symValue := 100, addend := 1, base := 0xdead, place := 0 })
    == (formula R_AARCH64_ABS64 { symValue := 100, addend := 1, base := 0xbeef, place := 0 })
#guard (formula R_AARCH64_ABS64    { symValue := 0xfeedface, addend := 0, base := 0, place := 0 })
        == some { value := 0xfeedface, size := 8 }
#guard (formula R_AARCH64_ABS32    { symValue := 0xc0ffee,   addend := 0, base := 0, place := 0 })
        == some { value := 0xc0ffee,   size := 4 }

-- Same shape for GLOB_DAT / JUMP_SLOT (S + A, 8 bytes).
#guard (formula R_AARCH64_GLOB_DAT  { symValue := 0xdeadbeef, addend := 0, base := 0, place := 0 })
        == some { value := 0xdeadbeef, size := 8 }
#guard (formula R_AARCH64_JUMP_SLOT { symValue := 0xb16b00b5, addend := 0, base := 0, place := 0 })
        == some { value := 0xb16b00b5, size := 8 }

-- UInt64 wraps modulo 2^64 (relevant for absolute relocs near
-- the top of the address space).
#guard (formula R_AARCH64_ABS64 { symValue := 0xFFFFFFFFFFFFFFFF, addend := 1, base := 0, place := 0 })
        == some { value := 0, size := 8 }

-- Compile-time unit test: the planner over a single-object link map
-- with one R_AARCH64_RELATIVE rela emits exactly one write.
section UnitTest
open LeanLoad.Test

private def relocLM : LeanLoad.Discover.LinkMap := {
  objects := #[synthObj "main"
    (rela := #[{
      r_offset := 0x1000
      r_info   := 1027   -- R_AARCH64_RELATIVE = type only, symIdx = 0
      r_addend := 0xa90
    }])]
}

#guard (LeanLoad.Plan.Reloc.plan formula relocLM #[0x10000]
          (LeanLoad.Plan.Resolve.buildTable relocLM)).size = 1

end UnitTest

end LeanLoad.Plan.Reloc.Aarch64

-- ============================================================================
-- Tests. The Reloc planner is parametric over the per-arch formula;
-- this suite exercises it on AArch64 (the only formula we have today),
-- so the test lives here next to the formula it instantiates with.
-- ============================================================================
namespace LeanLoad.Plan.Reloc.Test

/-- Relocation planner over `build/main`'s link map: with all-zero
    bases and a fresh resolution table, the planner emits one write
    per supported rela entry (skipping `R_AARCH64_NONE` and
    unsupported types). -/
def run (lm : LeanLoad.Discover.LinkMap) : IO Nat := do
  let mut failures := 0
  let rt := LeanLoad.Plan.Resolve.buildTable lm
  let bases : LeanLoad.Plan.Reloc.Bases := Array.replicate lm.objects.size 0
  let writes := LeanLoad.Plan.Reloc.plan
    LeanLoad.Plan.Reloc.Aarch64.formula lm bases rt
  if writes.size == 0 then
    IO.eprintln "expected nonzero relocation writes"
    failures := failures + 1
  return failures

end LeanLoad.Plan.Reloc.Test

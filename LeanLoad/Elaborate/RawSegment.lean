/-
The gabi-07 spec-level view of a PT_LOAD segment: byte-fields lifted
to typed values (`vaddr`, `memsz`, …, `perm`, `align`), gabi-07
per-segment invariants (`fileszLeMemsz`, `alignPow2`, `alignCong`),
and LeanLoad's 48-bit address bound. Nothing loader-specific — the
loader's page-aligned views live on `Segment` (which extends this).

Spec: gabi 07 (`third_party/gabi/docsrc/elf/07-pheader.rst`) § Program
Header.
-/

import LeanLoad.Parse.Structs

namespace LeanLoad.Elaborate

open LeanLoad.Parse (RawPhdr RawRela)

-- p_flags (gabi 07 Table: Segment Flag Bits)
def PF_X : UInt32 := 0x1
def PF_W : UInt32 := 0x2
def PF_R : UInt32 := 0x4

/-- Typed segment permission — generic 3-bit `read/write/execute`
    view. Decouples the gabi `PF_*` parse from the POSIX `PROT_*`
    that `mprotect` consumes; the latter mapping lives in
    `Plan.Layout`. -/
structure Prot where
  read  : Bool
  write : Bool
  exec  : Bool
  deriving Repr, BEq, Inhabited

instance : ToString Prot where
  toString p :=
    s!"{if p.read then "r" else "-"}\
       {if p.write then "w" else "-"}\
       {if p.exec then "x" else "-"}"

/-- Lift `p_flags` (gabi `PF_*` bits) to typed `Prot`. -/
def Prot.ofFlags (flags : UInt32) : Prot :=
  { read  := (flags &&& PF_R) != 0
    write := (flags &&& PF_W) != 0
    exec  := (flags &&& PF_X) != 0 }

/-- The segment's memory range fully contains the rela's 8-byte
    write window. Conservatively reserves 8 bytes. -/
def coversRela (vaddr memsz : UInt64) (r : RawRela) : Prop :=
  vaddr.toNat ≤ r.r_offset.toNat ∧
  r.r_offset.toNat + 8 ≤ vaddr.toNat + memsz.toNat

instance (vaddr memsz : UInt64) (r : RawRela) : Decidable (coversRela vaddr memsz r) := by
  unfold coversRela; infer_instance

end LeanLoad.Elaborate

-- Phdr-namespace alias so `elaborate`'s rela-bucketing can phrase the
-- witness on the raw phdr it's currently iterating over.
namespace LeanLoad.Parse.RawPhdr

open LeanLoad.Parse (RawPhdr RawRela)
open LeanLoad.Elaborate (coversRela)

@[reducible] def containsRela (p : RawPhdr) (r : RawRela) : Prop :=
  coversRela p.p_vaddr p.p_memsz r

end LeanLoad.Parse.RawPhdr

namespace LeanLoad.Elaborate

open LeanLoad.Parse (RawPhdr RawRela)

/-- The gabi-07 spec-level view of a PT_LOAD segment: byte-fields
    lifted to typed values, gabi-07 per-segment invariants, and
    LeanLoad's 48-bit address bound. No loader/page-alignment
    concerns — those live on `Segment` (which `extends RawSegment`). -/
structure RawSegment where
  /-- gabi `p_vaddr` — virtual address in process memory. -/
  vaddr  : UInt64
  /-- gabi `p_memsz` — total memory size in process. -/
  memsz  : UInt64
  /-- gabi `p_filesz` — file-backed size; `[filesz, memsz)` is BSS. -/
  filesz : UInt64
  /-- gabi `p_offset` — file offset of segment's bytes. -/
  offset : UInt64
  /-- gabi `p_flags` lifted to typed `Prot`. -/
  perm   : Prot
  /-- gabi `p_align`. -/
  align  : UInt64
  /-- gabi 07: `p_filesz ≤ p_memsz`. -/
  fileszLeMemsz : filesz ≤ memsz
  /-- gabi 07: `p_align` is `0` or a power of two. -/
  alignPow2 : align = 0 ∨ (align &&& (align - 1)) = 0
  /-- gabi 07: `p_vaddr ≡ p_offset (mod p_align)`. -/
  alignCong : align = 0 ∨ vaddr % align = offset % align
  /-- 48-bit address-space bound. **Not gabi.** LeanLoad assumes
      Linux's 48-bit virtual-address ceiling and small page-sized
      alignment; the bound is what lets page-arithmetic proofs
      (downstream in `Segment`) ignore UInt64 wrap. -/
  addrBound : vaddr.toNat + memsz.toNat + align.toNat < 2 ^ 48
  /-- General `Rela` relocations. -/
  rela   : Array { r : RawRela // coversRela vaddr memsz r }
  /-- PLT relocations. -/
  jmprel : Array { r : RawRela // coversRela vaddr memsz r }

/-- Lift a decidable proposition into `Except` (with `PLift` to bridge
    `Prop` through `Except`'s `Type` parameter). -/
private def assertProp (p : Prop) [Decidable p] (msg : String) :
    Except String (PLift p) :=
  if h : p then .ok ⟨h⟩ else .error msg

/-- Smart constructor: build a `RawSegment` from a `RawPhdr` (assumed
    PT_LOAD by the caller — `Elaborate.elaborate` filters its input
    array by `p_type`) and pre-located rela arrays. Decidably checks
    the gabi-07 per-segment invariants and LeanLoad's 48-bit address
    bound. No loader concerns. -/
def RawSegment.ofPhdr (phdr : RawPhdr)
    (rela jmprel : Array { r : RawRela // coversRela phdr.p_vaddr phdr.p_memsz r }) :
    Except String RawSegment := do
  let ⟨fileszLeMemsz⟩ ← assertProp (phdr.p_filesz ≤ phdr.p_memsz)
    s!"p_filesz=0x{phdr.p_filesz.toNat} > p_memsz=0x{phdr.p_memsz.toNat} \
       (gabi-07 § Program Header)"
  let ⟨alignPow2⟩ ← assertProp
    (phdr.p_align = 0 ∨ (phdr.p_align &&& (phdr.p_align - 1)) = 0)
    s!"p_align=0x{phdr.p_align.toNat} is not a power of 2 \
       (gabi-07 § Program Header)"
  let ⟨alignCong⟩ ← assertProp
    (phdr.p_align = 0 ∨ phdr.p_vaddr % phdr.p_align = phdr.p_offset % phdr.p_align)
    "alignment congruence violated (gabi-07: p_vaddr ≡ p_offset mod p_align)"
  let ⟨addrBound⟩ ← assertProp
    (phdr.p_vaddr.toNat + phdr.p_memsz.toNat + phdr.p_align.toNat < 2 ^ 48)
    s!"p_vaddr+p_memsz+p_align \
       (0x{phdr.p_vaddr.toNat}+0x{phdr.p_memsz.toNat}+0x{phdr.p_align.toNat}) \
       exceeds 48-bit bound"
  return {
    vaddr := phdr.p_vaddr, memsz := phdr.p_memsz,
    filesz := phdr.p_filesz, offset := phdr.p_offset,
    perm := Prot.ofFlags phdr.p_flags, align := phdr.p_align,
    fileszLeMemsz, alignPow2, alignCong, addrBound, rela, jmprel
  }

end LeanLoad.Elaborate

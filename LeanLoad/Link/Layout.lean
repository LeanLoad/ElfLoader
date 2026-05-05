/-
Layout planning — pure.

For Phase 2 (static loader) the input is a single parsed ELF; the output
is a list of mmap regions plus the entry-point address. No relocations,
no symbol resolution.

Spec basis: gabi 07 §§ Program Header, Base Address, Segment Permissions.
-/

import LeanLoad.Parse
import LeanLoad.Discover

namespace LeanLoad.Link.Layout

open LeanLoad.Parse

-- ============================================================================
-- Region: one mmap chunk, with the bytes to copy from the source ELF.
-- ============================================================================

/-- A single planned mmap region.

    `vaddr` and `length` describe the mapping itself.
    `fileOff`/`fileLen` describe how many bytes from the source ELF
    should be copied into the region starting at `vaddr - aligned base`;
    the tail (BSS) is left zero by anonymous mmap. -/
structure Mapping where
  /-- Page-aligned base address (mmap target). -/
  vaddr   : UInt64
  /-- mmap length in bytes (page-aligned). -/
  length  : UInt64
  /-- PROT_* bits for the final mprotect. -/
  prot    : UInt32
  /-- File offset to start copying bytes from. -/
  fileOff : UInt64
  /-- Number of bytes to copy (≤ `length`; remainder is BSS, left zero). -/
  fileLen : UInt64
  /-- Offset within the region where the copied bytes begin (handles the
      case `p_vaddr` is not page-aligned). -/
  pageInset : UInt64
  deriving Repr

-- ============================================================================
-- PF_* → PROT_* translation
-- ============================================================================

/-- Translate program-header permissions (gabi 07 § Segment Permissions)
    to the corresponding `PROT_*` bits for `mprotect`. The bit
    positions are swapped between PF_* and PROT_*: `PF_X=1, PF_W=2,
    PF_R=4` vs `PROT_READ=1, PROT_WRITE=2, PROT_EXEC=4`, so each
    flag must be translated explicitly. -/
def protOfFlags (pflags : UInt32) : UInt32 :=
  let r := if (pflags &&& Program.PF_R) != 0 then (1 : UInt32) else 0
  let w := if (pflags &&& Program.PF_W) != 0 then (2 : UInt32) else 0
  let x := if (pflags &&& Program.PF_X) != 0 then (4 : UInt32) else 0
  r ||| w ||| x

#guard protOfFlags (Program.PF_R ||| Program.PF_X) = 5  -- PROT_READ|EXEC
#guard protOfFlags (Program.PF_R ||| Program.PF_W) = 3  -- PROT_READ|WRITE
#guard protOfFlags Program.PF_R = 1                     -- PROT_READ only

#guard protOfFlags (Program.PF_R + Program.PF_X) = 5  -- PROT_READ|PROT_EXEC

-- ============================================================================
-- Page alignment helpers
-- ============================================================================

/-- Round `x` down to a multiple of `align`. `align` must be a power of two
    (or zero, treated as 1). -/
def alignDown (x align : UInt64) : UInt64 :=
  if align == 0 then x else x - (x % align)

/-- Round `x` up to a multiple of `align`. -/
def alignUp (x align : UInt64) : UInt64 :=
  if align == 0 then x else alignDown (x + align - 1) align

#guard alignDown 0x1234 0x1000 == 0x1000
#guard alignUp 0x1234 0x1000 == 0x2000

-- ============================================================================
-- Plan construction (Phase 2: single static binary)
-- ============================================================================

/-- Build a layout mapping from a `PT_LOAD` program header. -/
def mappingOfPhdr (ph : Program.Header64) : Mapping :=
  let align := if ph.p_align == 0 then 1 else ph.p_align
  let baseAligned := alignDown ph.p_vaddr align
  let endAddr     := ph.p_vaddr + ph.p_memsz
  let endAligned  := alignUp endAddr align
  let pageInset   := ph.p_vaddr - baseAligned
  { vaddr     := baseAligned
    length    := endAligned - baseAligned
    prot      := protOfFlags ph.p_flags
    fileOff   := ph.p_offset
    fileLen   := ph.p_filesz
    pageInset := pageInset }

-- ============================================================================
-- Per-object and combined plans
--
-- For each object in a discovered closure, compute its set of mmap
-- mappings plus a `preferredBase` hint:
--   * `ET_EXEC` (non-PIE): mappings sit at absolute `p_vaddr`,
--     `preferredBase = 0` means "honour those addresses literally".
--   * `ET_DYN`  (PIE / shared): `p_vaddr` is relative to a base the
--     kernel will choose at `mmap` time. `preferredBase = 0` means
--     "let the kernel pick".
-- ============================================================================

/-- Layout for a single loaded object. -/
structure ObjectLayout where
  objectIdx     : Nat
  /-- Preferred base address. 0 = honour `p_vaddr` (ET_EXEC) or let the
      kernel choose (ET_DYN). -/
  preferredBase : UInt64
  /-- mmap mappings whose `vaddr` is **relative to the chosen base**
      for `ET_DYN`, or absolute for `ET_EXEC`. -/
  mappings      : Array Mapping
  /-- The `e_entry` field. `none` for objects we never enter
      (e.g. shared libraries). -/
  entry         : Option UInt64
  /-- True for the main executable. -/
  isMain        : Bool
  deriving Repr

/-- Layout for a single parsed ELF, given its index in the
    `Closure.objects` array. -/
def objectLayout (objectIdx : Nat) (isMain : Bool) (elf : File.ParsedElf) : ObjectLayout :=
  let loads    := elf.phdrs.filter (·.p_type == Program.PT_LOAD)
  let mappings := loads.map mappingOfPhdr
  let entry    := if isMain then some elf.header.e_entry else none
  { objectIdx, preferredBase := 0, mappings, entry, isMain }

/-- The unified plan: per-object layouts plus init/fini orders.

    Relocations are not part of `LoaderPlan` — they depend on the
    actual chosen bases and are computed at load time via
    `Link.Reloc.plan`. The single-static case is just a `LoaderPlan`
    with one layout, no init/fini. -/
structure LoaderPlan where
  layouts   : Array ObjectLayout
  initOrder : Array Nat
  finiOrder : Array Nat
  deriving Repr

/-- Plan for a discovered closure. The first object (index 0) is main.
    A single-element closure (a static binary with no `DT_NEEDED`) is
    just the N=1 case of this. -/
def fromClosure (cl : Discover.Closure) (initOrder finiOrder : Array Nat) : LoaderPlan :=
  let layouts : Array ObjectLayout := Id.run do
    let mut acc : Array ObjectLayout := Array.mkEmpty cl.objects.size
    let mut idx := 0
    for obj in cl.objects do
      acc := acc.push (objectLayout idx (idx == 0) obj.elf)
      idx := idx + 1
    return acc
  { layouts, initOrder, finiOrder }

end LeanLoad.Link.Layout

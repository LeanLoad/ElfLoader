/-
Layout planning — pure.

Two algorithms, both consumed by the `Layout` stage and bundled into
the `Layout` struct:

  1. Per-object mmap layout: walk `PT_LOAD`s, compute page-aligned
     mappings + their `PROT_*` bits.
  2. Init/fini order: DFS post-order over the `DT_NEEDED` graph
     (gabi 08 § Initialization and Termination Functions). Cycles
     are broken by a visited set; total via fuel.

Spec basis: gabi 07 §§ Program Header, Base Address, Segment
Permissions; gabi 08 § Initialization and Termination Functions.
-/

import LeanLoad.Spec.Program
import LeanLoad.Parse.File
import LeanLoad.Discover
import LeanLoad.TestFixture

namespace LeanLoad.Layout

open LeanLoad.Spec
open LeanLoad

-- ============================================================================
-- One mmap chunk, with the bytes to copy from the source ELF.
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
-- Already aligned: identity.
#guard alignDown 0x1000 0x1000 == 0x1000
#guard alignUp   0x1000 0x1000 == 0x1000
-- align = 0 ⇒ identity (no rounding).
#guard alignDown 0x1234 0 == 0x1234
#guard alignUp   0x1234 0 == 0x1234

-- ============================================================================
-- Per-object layout (mappings + entry)
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

-- Page-aligned vaddr at 0x1000, fits in one 0x1000 page → no inset.
#guard
  let m := mappingOfPhdr { (default : Program.Header64) with
    p_vaddr := 0x1000, p_memsz := 0x800, p_filesz := 0x800,
    p_align := 0x1000, p_flags := Program.PF_R ||| Program.PF_X,
    p_offset := 0x1000 }
  m.vaddr = 0x1000 ∧ m.length = 0x1000 ∧ m.pageInset = 0 ∧ m.prot = 5
-- Unaligned vaddr 0x1234 with 0x1000 alignment: round-down to 0x1000,
-- pageInset = 0x234, length covers up to next page boundary after end.
#guard
  let m := mappingOfPhdr { (default : Program.Header64) with
    p_vaddr := 0x1234, p_memsz := 0x100, p_filesz := 0x100,
    p_align := 0x1000, p_flags := Program.PF_R ||| Program.PF_W,
    p_offset := 0x1234 }
  m.vaddr = 0x1000 ∧ m.length = 0x1000 ∧ m.pageInset = 0x234 ∧ m.prot = 3
-- p_align = 0 ⇒ treat as 1 (no alignment, identity).
#guard
  let m := mappingOfPhdr { (default : Program.Header64) with
    p_vaddr := 0x42, p_memsz := 0x10, p_filesz := 0x10,
    p_align := 0, p_flags := Program.PF_R }
  m.vaddr = 0x42 ∧ m.length = 0x10 ∧ m.pageInset = 0
-- p_memsz > p_filesz (BSS tail): length covers memsz, fileLen tracks
-- only the file-backed portion.
#guard
  let m := mappingOfPhdr { (default : Program.Header64) with
    p_vaddr := 0x2000, p_memsz := 0x800, p_filesz := 0x200,
    p_align := 0x1000, p_flags := Program.PF_R ||| Program.PF_W,
    p_offset := 0x2000 }
  m.fileLen = 0x200 ∧ m.length = 0x1000

/-- Layout for a single loaded object.

    For `ET_EXEC`: mappings sit at absolute `p_vaddr`,
    `preferredBase = 0` means "honour those addresses literally".
    For `ET_DYN` (PIE / shared): `p_vaddr` is relative to a base the
    kernel will choose at `mmap` time. `preferredBase = 0` means
    "let the kernel pick". -/
structure ObjectLayout where
  objectIdx     : Nat
  preferredBase : UInt64
  mappings      : Array Mapping
  /-- The `e_entry` field. `none` for objects we never enter
      (e.g. shared libraries). -/
  entry         : Option UInt64
  /-- True for the main executable. -/
  isMain        : Bool
  deriving Repr

/-- Layout for a single parsed ELF, given its index in the
    `LinkMap.objects` array. -/
def objectLayout (objectIdx : Nat) (isMain : Bool) (elf : Parse.File.ParsedElf) : ObjectLayout :=
  let loads    := elf.phdrs.filter (·.p_type == Program.PT_LOAD)
  let mappings := loads.map mappingOfPhdr
  let entry    := if isMain then some elf.header.e_entry else none
  { objectIdx, preferredBase := 0, mappings, entry, isMain }

-- ============================================================================
-- Init / fini order: DFS post-order over `DT_NEEDED`. Spec: gabi 08
-- § Initialization and Termination Functions.
--
-- > Before the initialization functions for any object A is called,
-- > the initialization functions for any other objects that object A
-- > depends on are called. … The order of initialization for circular
-- > dependencies is undefined.
--
-- Output: `Array Nat` of `LinkMap.objects` indices. Init runs them in
-- order; fini runs them in reverse.
-- ============================================================================

/-- Find the index of an object whose `name` matches one of `nameOrSoname`.
    Used to follow `DT_NEEDED` strings to their loaded objects. -/
private def findObject (lm : Discover.LinkMap) (name : String) : Option Nat :=
  lm.objects.findIdx? (·.name == name)

/-- Depth-first traversal helper. `visited[i]` marks an object that
    has either been emitted (`order` already contains it) or is
    currently in the descent path (cycle protection).

    `fuel` bounds the recursion depth and lets Lean mechanically
    discharge termination. The caller (`initOrder`) seeds it with
    `lm.objects.size`, which is sufficient because each recursive
    call descends through one not-yet-visited object, and there are
    at most `lm.objects.size` of those. With this, no `partial def`
    is needed — `dfs` is structurally recursive on `fuel`. -/
private def dfs (fuel : Nat) (lm : Discover.LinkMap)
    (idx : Nat) (visited : Array Bool) (order : Array Nat) : Array Bool × Array Nat :=
  match fuel with
  | 0 => (visited, order)
  | fuel + 1 => Id.run do
    if h : idx < visited.size then
      if visited[idx] then return (visited, order)
    else
      return (visited, order)
    let mut visited := visited.set! idx true
    let mut order := order
    let some obj := lm.objects[idx]? | return (visited, order)
    for needed in obj.elf.needed do
      if let some childIdx := findObject lm needed then
        let (v', o') := dfs fuel lm childIdx visited order
        visited := v'
        order := o'
    order := order.push idx
    return (visited, order)
termination_by fuel

/-- Compute init order: depth-first post-order from object 0 (main).
    Result is an array of object indices to invoke in sequence. -/
def initOrder (lm : Discover.LinkMap) : Array Nat :=
  let n := lm.objects.size
  if n == 0 then #[]
  else
    let visited := Array.replicate n false
    let order : Array Nat := Array.mkEmpty n
    (dfs n lm 0 visited order).snd

/-- Termination order (`DT_FINI_ARRAY`, `DT_FINI`). Reverse of init. -/
def finiOrder (lm : Discover.LinkMap) : Array Nat :=
  (initOrder lm).reverse

-- ============================================================================
-- Bundled output: layouts + init/fini order. The output of the
-- Layout stage; consumed by Map / Reloc / Apply / Init / Exec.
--
-- Relocations are not part of `Layout` — they depend on actual chosen
-- bases and are computed post-Map by `LeanLoad.Reloc.plan`.
-- ============================================================================

/-- The unified Layout-stage output. -/
structure Layout where
  layouts   : Array ObjectLayout
  initOrder : Array Nat
  finiOrder : Array Nat
  deriving Repr

/-- Build the Layout for a discovered link map. The first object
    (index 0) is main. A single-element link map (a static binary
    with no `DT_NEEDED`) is just the N=1 case of this. -/
def fromLinkMap (lm : Discover.LinkMap) (initOrder finiOrder : Array Nat) : Layout :=
  { layouts   := lm.objects.mapIdx fun idx obj => objectLayout idx (idx = 0) obj.elf
    initOrder
    finiOrder }

-- Empty-link map edge case (the strong size-equality is in `LeanLoad.Thm`).
#guard (fromLinkMap { objects := #[] } #[] #[]).layouts.isEmpty

-- ============================================================================
-- Compile-time unit tests on synthetic link maps (`synthObj` from
-- `LeanLoad.TestFixture`).
-- ============================================================================
section UnitTest
open LeanLoad.Test

private def emptyLM   : Discover.LinkMap := { objects := #[] }
private def loneLM    : Discover.LinkMap := { objects := #[synthObj "main"] }
private def chainLM   : Discover.LinkMap := { objects := #[
  synthObj "main"      (needed := #["libfoo.so"]),
  synthObj "libfoo.so" (needed := #["libbar.so"]),
  synthObj "libbar.so"
] }
/-- Diamond: main needs libfoo + libbar; both need libcommon (visited
    once). Post-order = `[3, 1, 2, 0]`. -/
private def diamondLM : Discover.LinkMap := { objects := #[
  synthObj "main"         (needed := #["libfoo.so", "libbar.so"]),
  synthObj "libfoo.so"    (needed := #["libcommon.so"]),
  synthObj "libbar.so"    (needed := #["libcommon.so"]),
  synthObj "libcommon.so"
] }
/-- Cycle libA ↔ libB. Order is implementation-defined (gabi 08 says
    "undefined for circular dependencies") — we just check the visited
    set terminates and emits every node exactly once. -/
private def cycleLM   : Discover.LinkMap := { objects := #[
  synthObj "main"    (needed := #["libA.so"]),
  synthObj "libA.so" (needed := #["libB.so"]),
  synthObj "libB.so" (needed := #["libA.so"])
] }

#guard initOrder emptyLM   = #[]
#guard finiOrder emptyLM   = #[]
#guard initOrder loneLM    = #[0]
#guard initOrder chainLM   = #[2, 1, 0]
#guard finiOrder chainLM   = #[0, 1, 2]
#guard initOrder diamondLM = #[3, 1, 2, 0]
#guard (initOrder cycleLM).size = 3

end UnitTest

end LeanLoad.Layout

-- ============================================================================
-- IO test runner. Init order: post-order DFS. Main (idx 0) is the
-- root, so it must appear last (after all of its transitive deps).
-- ============================================================================
namespace LeanLoad.Layout.Test

open LeanLoad

def run (lm : Discover.LinkMap) : IO Nat := do
  let mut failures := 0
  let order := initOrder lm
  if order.size != lm.objects.size then
    IO.eprintln s!"init order size {order.size} ≠ object count {lm.objects.size}"
    failures := failures + 1
  if order.back? != some 0 then
    IO.eprintln s!"main (idx 0) should be last in init order; got {order}"
    failures := failures + 1
  return failures

end LeanLoad.Layout.Test

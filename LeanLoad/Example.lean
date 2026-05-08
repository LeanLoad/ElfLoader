/-
Cross-stage walkthrough of LeanLoad's pipeline with synthetic inputs.

Per-stage unit `#guard`s next to each definition cover positive and
edge cases for *that* unit. This file covers *integration* across
stages plus boundary-rejection cases that span more than one file:

  1. `Inhabited Elf` and `synthElf` — fixtures used below. Production
     never builds an `Elf` without going through `elaborate`; these
     synthesize partial Elfs for the compile-time `#guard`s.

  2. **Elaborate boundary** — `RawElf → Except String Elf`. The
     rejection paths a malformed binary takes through `elaborate`.

  3. **Plan walkthrough** — symbol resolution (`Plan/Resolve`),
     base assignment (`Plan/Layout`), and the `Region` view over a
     segment with a chosen base.

  4. **Realize plan** — the `Array MemoryOp` that `Exec.realize`
     interprets. Shows how `Region.ops` shapes change with BSS-only
     vs file+BSS segments, and how `Realize.planOps` concatenates
     mmap + patch + ctor ops into one list.

`LeanLoad/Test.lean` exercises the real `examples/build/main`
end-to-end; that remains the authoritative "the loader copes with
musl-gcc's actual output" check. This file trades fidelity for
synthesis-driven readability.
-/

import LeanLoad.Plan.Layout
import LeanLoad.Plan.Realize
import LeanLoad.Plan.Resolve
import LeanLoad.Elaborate.Elf

namespace LeanLoad.Example

open LeanLoad
open LeanLoad.Elaborate
open LeanLoad.Layout

-- ============================================================================
-- 1. Test fixtures.
-- ============================================================================

/-- Default `Elf` — empty in every dimension. Used only by tests that
    synthesize an `Elf` and override the few fields the test cares
    about; production code always goes through `elaborate`. -/
instance : Inhabited Elaborate.Elf where
  default :=
    { elfType := .none, machine := .x86_64,
      entry := 0, phoff := 0, phnum := 0,
      symtab := #[], needed := #[],
      soname := Option.none, runpath := Option.none, initArr := #[],
      segments := #[],
      segmentsSorted := by decide,
      segmentsNonOverlap := by decide }

/-- Synthetic `Elf` with overrides for the fields a test cares about. -/
def synthElf
    (elfType : Elaborate.ElfType        := .none)
    (needed  : Array String             := #[])
    (symtab  : Array Elaborate.Symbol   := #[])
    (segments : Array Elaborate.Segment := #[])
    (segmentsSorted : Sorted segments        := by decide)
    (segmentsNonOverlap : NonOverlap segments := by decide) : Elaborate.Elf :=
  { (default : Elaborate.Elf) with
    elfType, needed, symtab, segments,
    segmentsSorted, segmentsNonOverlap }

-- ============================================================================
-- 2. Elaborate boundary: `RawElf → Except String Elf`.
--
-- Magic and byte-decode shape are checked at *parse* time; a
-- malformed magic prefix never produces a `RawElf` (see the example
-- block in `Parse/Structs.lean`). The four cases below are the ones
-- `elaborate` itself enforces.
-- ============================================================================

/-- Header for a 64-bit, little-endian, x86-64, ET_DYN ELF — the
    minimum that lets `elaborate` past the header sanity gates. -/
private def goodHeader : Parse.RawEhdr := { (default : Parse.RawEhdr) with
  ident := { (default : Parse.RawIdent) with
             ei_class := ELFCLASS64, ei_data := ELFDATA2LSB }
  e_type    := 3,    -- ET_DYN
  e_machine := 62 }  -- EM_X86_64

/-- Smallest `RawElf` `elaborate` can succeed on: no PT_LOAD, no
    relas, just a sane header. -/
private def emptyRawElf : Parse.RawElf := { (default : Parse.RawElf) with
  header := goodHeader }

#guard (elaborate emptyRawElf).toOption.isSome

-- Rejection: `ei_class != ELFCLASS64` (we only support 64-bit).
private def class32 : Parse.RawElf := { emptyRawElf with
  header := { emptyRawElf.header with ident :=
    { emptyRawElf.header.ident with ei_class := 1 /- ELFCLASS32 -/ } } }
#guard (elaborate class32).toOption.isNone

-- Rejection: big-endian (only ELFDATA2LSB supported).
private def bigEndian : Parse.RawElf := { emptyRawElf with
  header := { emptyRawElf.header with ident :=
    { emptyRawElf.header.ident with ei_data := 2 /- ELFDATA2MSB -/ } } }
#guard (elaborate bigEndian).toOption.isNone

-- Rejection: unsupported `e_machine` (e.g. EM_RISCV = 243).
private def riscv : Parse.RawElf := { emptyRawElf with
  header := { emptyRawElf.header with e_machine := 243 } }
#guard (elaborate riscv).toOption.isNone

-- Rejection: a rela whose offset doesn't sit inside any PT_LOAD.
-- With no PT_LOAD entries, every rela is uncovered.
private def relaWithNoCover : Parse.RawElf := { emptyRawElf with
  rela := #[{ r_offset := 0xdeadbeef, r_info := 0, r_addend := 0 }] }
#guard (elaborate relaWithNoCover).toOption.isNone

-- ============================================================================
-- 3. Plan walkthrough.
-- ============================================================================

-- ---- 3a. Symbol resolution: main refs `printf`, libc defines it. -----------

private def globalDef (name : String) (value : UInt64) : Symbol :=
  { name := some name, bind := .global, shndx := .concrete 1, value }

private def undef (name : String) : Symbol :=
  { name := some name, bind := .global, shndx := .undef, value := 0 }

private def resolveElfs : Array Elaborate.Elf := #[
  synthElf (needed := #["libc.so"])
           (symtab := #[default, undef "printf"]),
  synthElf (symtab := #[default, globalDef "printf" 0xc0ffee]) ]

#guard (Resolve.resolveByName resolveElfs "printf").map (·.objectIdx.val) = some 1
#guard (Resolve.resolveByName resolveElfs "missing")                      = none
#guard (Resolve.buildTable    resolveElfs).missing.size                   = 0

-- ---- 3b. Layout: base assignment + page-aligned stacking. ------------------

/-- Synthetic PT_LOAD segment built via `Segment.ofPhdr`. Returns
    `Option` because `ofPhdr` returns `Except` for ill-formed phdrs;
    well-formed inputs always succeed. -/
private def synthSegment? (vaddr memsz : UInt64) : Option Elaborate.Segment :=
  let phdr : Parse.RawPhdr := { (default : Parse.RawPhdr) with
    p_type := Parse.PT_LOAD,
    p_vaddr := vaddr, p_memsz := memsz,
    p_filesz := 0, p_offset := 0, p_align := 0x1000 }
  (Elaborate.Segment.ofPhdr phdr #[] #[]).toOption

-- `.exec` objects keep base 0; `.dyn` ones start at `dynAnchor`.
#guard assignBases #[synthElf (elfType := .exec)] = #[0]
#guard assignBases #[synthElf (elfType := .dyn)]  = #[dynAnchor]

-- Stacking: each `.dyn` lib has a 0x2000-byte span (one PT_LOAD at
-- vaddr 0 of memsz 0x2000 → pageEndAddr 0x2000), `advance =
-- alignUp 0x2000 0x1000 = 0x2000`. So libfoo gets `dynAnchor`,
-- libbar gets `dynAnchor + 0x2000`. The `.exec` keeps base 0 and
-- doesn't move the cursor.
private def stackingExample : Option (Array UInt64) := do
  let seg ← synthSegment? 0 0x2000
  let libElf := synthElf (elfType := .dyn) (segments := #[seg])
  some (assignBases #[ synthElf (elfType := .exec), libElf, libElf ])

#guard stackingExample = some #[0, dynAnchor, dynAnchor + 0x2000]

-- ============================================================================
-- 4. Realize plan: `Region` views and `Array MemoryOp` shapes.
--
-- `Region` (a Segment with chosen base) is the unit `Realize` plans
-- around. `Region.ops` emits the per-region kernel calls; the shape
-- of the emitted list depends on the segment's BSS profile.
-- ============================================================================

-- ---- 4a. Region view: absolute addresses derive from base + segment. -------

/-- A 0x2000-byte BSS-only segment at vaddr 0 (page-aligned). With
    `filesz = 0` and `memsz = 0x2000`, this is two pages of pure BSS
    with no file backing. -/
private def bssOnlySeg : Option Segment :=
  let phdr : Parse.RawPhdr := { (default : Parse.RawPhdr) with
    p_type := Parse.PT_LOAD,
    p_vaddr := 0, p_memsz := 0x2000,
    p_filesz := 0, p_offset := 0, p_align := 0x1000 }
  (Segment.ofPhdr phdr #[] #[]).toOption

-- A region with the BSS-only segment placed at `dynAnchor`.
private def bssOnlyRegion : Option Region :=
  bssOnlySeg.map fun seg => { base := dynAnchor, seg }

-- The region's mmap'd range is `[base, base + 0x2000)`.
#guard bssOnlyRegion.map (·.absVaddr) = some dynAnchor
#guard bssOnlyRegion.map (·.length)   = some 0x2000

-- BSS-only: no file backing, no partial-page zero (everything covered
-- by the anon reservation, which is kernel-zero-filled).
#guard bssOnlyRegion.map (·.hasFileBacked) = some false
#guard bssOnlyRegion.map (·.hasPartialBss) = some false

-- ---- 4b. Region.ops shape — `#guard`-able since `MemoryOp` is pure. ------
--
-- `Realize.Region.ops fileIdx r` emits ops shaped per the segment's
-- BSS profile. Sizes:
--
--   BSS-only  (filesz=0):              [mmapAnon, mprotect]              (2)
--   file-only (filesz=memsz, aligned): [mmapAnon, mmapFile, mprotect]    (3)
--   file+BSS  (filesz<memsz, partial): [mmapAnon, mmapFile,
--                                       zeroout, mprotect]               (4)

/-- A more general synth helper that lets us vary `filesz` to land in
    each profile. -/
private def synthSeg? (vaddr memsz filesz : UInt64) : Option Segment :=
  let phdr : Parse.RawPhdr := { (default : Parse.RawPhdr) with
    p_type := Parse.PT_LOAD,
    p_vaddr := vaddr, p_memsz := memsz,
    p_filesz := filesz, p_offset := 0, p_align := 0x1000 }
  (Segment.ofPhdr phdr #[] #[]).toOption

private def fileOnlySeg : Option Segment := synthSeg? 0 0x1000 0x1000  -- one page, fully file
private def mixedSeg    : Option Segment := synthSeg? 0 0x2000 0x800   -- file then BSS

private def regionOps (seg : Option Segment) : Option (Array (MemoryOp 1)) :=
  seg.map fun s => Realize.Region.ops ⟨0, by simp⟩ ({ base := dynAnchor, seg := s } : Region)

#guard (regionOps bssOnlySeg).map (·.size)  = some 2
#guard (regionOps fileOnlySeg).map (·.size) = some 3
#guard (regionOps mixedSeg).map (·.size)    = some 4

-- ---- 4c. End-to-end planOps: realize ++ patches. -------------------------
--
-- Ctors are user-code execution (not kernel ops); they run inline
-- in `Main.realize` after `MemoryOp.runAll`, so they're not in
-- `planOps`'s output.

-- An empty graph: no elfs, no patches → empty op list.
#guard (Realize.planOps #[] #[] (by decide) #[]).size = 0

end LeanLoad.Example

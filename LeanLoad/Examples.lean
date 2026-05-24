/-
Cross-stage walkthrough of LeanLoad's pipeline with synthetic inputs.

Per-stage unit `#guard`s next to each definition cover positive and
edge cases for *that* unit. This file covers *integration* across
stages plus boundary-rejection cases that span more than one file:

  1. `Inhabited Elf` and `synthElf` — fixtures used below. Production
     never builds an `Elf` without going through checked `Parse.parse`;
     these synthesize partial Elfs for the compile-time `#guard`s.

  2. **Checked parse boundary** — synthetic ELF bytes accepted by
     `Parse.parseM`, surfacing the checked `Elf` fields.

  3. **Resolve/Layout walkthrough** — symbol resolution (`Resolve`),
     base assignment (`Layout`), and the `SegmentLayout` view
     over a segment (base-free).

  4. **Exec** — the structured `LoadOps` tree that
     `Main.realize` runs. Shows how
     `Exec.setupSegment` shapes change with BSS-only vs file+BSS
     segments, and how `Exec.build` constructs intrinsic-safe load ops.

`./run.sh` exercises the real `examples/build/main` end-to-end —
that remains the authoritative "the loader copes with musl-gcc's
actual output" check. This file trades fidelity for synthesis-
driven readability.
-/

import LeanLoad.Layout.Basic
import LeanLoad.Reloc
import LeanLoad.Reloc.Symbol
import LeanLoad.Exec.Build
import LeanLoad.Parse.Examples

namespace LeanLoad.Examples

open LeanLoad
open LeanLoad.Parse
open LeanLoad.Layout

-- ============================================================================
-- 1. Test fixtures.
-- ============================================================================

/-- Synthetic reservation base used by examples that don't need a
    real kernel-picked address. Production loads use the address
    returned by `Runtime.mmapAnonAlloc`. -/
private def exampleAnchor : UInt64 := 0x80000000

private def exampleFileSize : UInt64 := 0x100000

private def syntheticHeader (elfType : Parse.ElfType) (notExec : elfType ≠ .exec) :
    ElfHeader :=
  { ident :=
      { magic := .elf,
        ei_class := .class64,
        ei_data := .lsb,
        ei_version := .current,
        ei_osabi := .none,
        ei_abiversion := default,
        pad0 := 0, pad1 := 0, pad2 := 0, pad3 := 0, pad4 := 0, pad5 := 0, pad6 := 0 },
    e_type := elfType,
    e_machine := .x86_64,
    e_version := .current,
    e_entry := 0,
    e_phoff := 0,
    e_shoff := 0,
    e_flags := 0,
    e_ehsize := 64,
    e_phentsize := 56,
    e_phnum := 0,
    e_shentsize := 0,
    e_shnum := 0,
    e_shstrndx := .undef,
    class64 := rfl,
    littleEndian := rfl,
    ehsizeOk := by decide,
    phentsizeOk := by decide,
    notExec }

/-- Default `Elf` — empty in every dimension. Used only by tests that
    synthesize an `Elf` and override the few fields the test cares
    about; production code always goes through `Parse.parse`. -/
instance : Inhabited Elf where
  default :=
    { header := syntheticHeader .none (by decide),
      symtab := #[], needed := #[],
      soname := Option.none, runpath := Option.none,
      segments := SegmentTable.empty,
      relocs := { rela := #[], jmprel := #[] },
      initArr := #[], finiArr := #[] }

/-- Synthetic `Elf` with overrides for the fields a test cares about. -/
def synthElf
    (header  : ElfHeader                := syntheticHeader .none (by decide))
    (needed  : Array String             := #[])
    (symtab  : Array Parse.Symbol       := #[])
    (segments : Parse.SegmentTable          := SegmentTable.empty)
    (relocs : Dynamic.Reloc.RelocTable segments :=
      { rela := #[], jmprel := #[] }) : Elf :=
  { (default : Elf) with
    header,
    needed, symtab,
    segments,
    relocs,
    initArr := #[], finiArr := #[] }

-- ============================================================================
-- 2. Checked parse boundary.
-- ============================================================================

-- Real-world acceptance: the 488-byte hand-crafted ELF fixture
-- (`Parse.Examples.fixtureBytes` → `Parse.Examples.fixture`) is a
-- library-shaped ET_DYN with strtab, symtab, DT_HASH, rela,
-- init_array, and a 12-entry dynamic table — engineered to satisfy
-- every checked-parse invariant.
#guard match Parse.Examples.fixture with
       | .ok elf =>
           elf.header.e_type    == .dyn
        && elf.header.e_machine == .x86_64
        && elf.header.e_entry   == 0x100
        && elf.segments.items.size == 1           -- single PT_LOAD
        && elf.needed.size == 1                   -- DT_NEEDED "libc.so.6"
        && elf.initArr.size == 1                  -- one ctor
       | .error _ => false

-- ============================================================================
-- 3. Resolve/Layout walkthrough.
-- ============================================================================

-- ---- 3a. Symbol resolution: main refs `printf`, libc defines it. -----------

private def globalDef (name : String) (value : UInt64) : Symbol :=
  { name, bind := .global, shndx := .concrete 1, value }

private def undef (name : String) : Symbol :=
  { name, bind := .global, shndx := .undef, value := 0 }

private def resolveElfs : Array Elf := #[
  synthElf (needed := #["libc.so"])
           (symtab := #[default, undef "printf"]),
  synthElf (symtab := #[default, globalDef "printf" 0xc0ffee]) ]

private def loadedObject (name : String) (elf : Elf) :
    Discover.LoadedObject :=
  { name, handle := (default : Runtime.File), elf }

private def resolveGraph : Discover.LoadGraph :=
  { objects := #[
      loadedObject "main" resolveElfs[0]!,
      loadedObject "libc.so" resolveElfs[1]! ],
    deps := #[#[1], #[]],
    initOrder := #[⟨1, by decide⟩, ⟨0, by decide⟩],
    sizePos := by decide,
    namesNodup := by native_decide,
    depsSize := by decide,
    depsBounds := by decide,
    closure := by decide,
    initOrderSize := by decide,
    initOrderNodup := by decide }

#guard
  (Reloc.Symbol.resolveByName resolveGraph (Reloc.Symbol.bfsOrder resolveGraph) "printf").map
      (·.objectIdx.val) = some 1
#guard
  Reloc.Symbol.resolveByName resolveGraph (Reloc.Symbol.bfsOrder resolveGraph) "missing" = none
#guard (Reloc.Result.ofGraph resolveGraph).isOk

-- ---- 3b. Layout: base assignment + page-aligned stacking. ------------------

/-- Synthetic PT_LOAD segment built via `Segment.ofPhdr`. Returns
    `Option` because `ofPhdr` returns `Except` for ill-formed programHeaders;
    well-formed inputs always succeed. -/
private def synthSegment? (eaddr : Eaddr) (memsz : ByteSize) : Option Parse.Segment :=
  let phdr : Parse.ProgramHeader := { (default : Parse.ProgramHeader) with
    p_type := .load,
    p_vaddr := eaddr, p_memsz := memsz,
    p_filesz := 0, p_offset := 0, p_align := 0x1000 }
  (Parse.Segment.ofPhdr phdr exampleFileSize).toOption

-- ET_EXEC is rejected during checked parse, so every elf reaching
-- planning is ET_DYN. `assignBases` takes the reservation base
-- as a parameter; production gets it from `Runtime.mmapAnon`.
#guard
  let elfs : Array Elf := #[synthElf (header := syntheticHeader .dyn (by decide))]
  match Layout.ofElfs elfs with
  | .ok lp => (assignBases exampleAnchor lp).toArray == #[exampleAnchor]
  | .error _ => false

-- Stacking: each `.dyn` lib has a 0x2000-byte span (one PT_LOAD at
-- eaddr 0 of memsz 0x2000 → pageEndAddr 0x2000), `advance =
-- alignUp 0x2000 0x1000 = 0x2000`. So three libs get
-- exampleAnchor, exampleAnchor + 0x2000, exampleAnchor + 0x4000.
private def stackingExample : Option (Array UInt64) := do
  let seg ← synthSegment? 0 0x2000
  let segments ← (SegmentTable.ofArray #[seg]).toOption
  let libElf := synthElf
    (header := syntheticHeader .dyn (by decide))
    (segments := segments)
  let elfs := #[libElf, libElf, libElf]
  match Layout.ofElfs elfs with
  | .ok lp => some ((assignBases exampleAnchor lp).toArray)
  | .error _ => none

#guard stackingExample = some #[exampleAnchor, exampleAnchor + 0x2000, exampleAnchor + 0x4000]

-- ============================================================================
-- 4. Realize plan: `SegmentLayout` views and LoadOps shapes.
--
-- `SegmentLayout` is the base-free loader view of a segment; absolute
-- addresses come from `base + sp.pageEaddr` at exec time.
-- ============================================================================

-- ---- 4a. SegmentLayout view: base-free page math. ----------------------------

/-- A 0x2000-byte BSS-only segment at eaddr 0 (page-aligned). With
    `filesz = 0` and `memsz = 0x2000`, this is two pages of pure BSS
    with no file backing. -/
private def bssOnlySeg : Option Segment :=
  let phdr : Parse.ProgramHeader := { (default : Parse.ProgramHeader) with
    p_type := .load,
    p_vaddr := 0, p_memsz := 0x2000,
    p_filesz := 0, p_offset := 0, p_align := 0x1000 }
  (Segment.ofPhdr phdr exampleFileSize).toOption

private def bssOnlyPlan : Option (SegmentLayout 0) :=
  bssOnlySeg.map (fun s => SegmentLayout.ofSegmentCore 0 s #[])

-- The plan's mmap'd range is `[pageEaddr, pageEaddr + pageLength)`,
-- absolute addresses computed as `base + pageEaddr`.
#guard bssOnlyPlan.map (·.pageEaddr)   = some 0
#guard bssOnlyPlan.map (·.pageLength)  = some 0x2000

-- BSS-only: no file backing — the underlying object reservation
-- already covers it (kernel zero-fills MAP_ANONYMOUS).
#guard bssOnlyPlan.map (·.hasFileBacked) = some false

-- ---- 4b. setupSegment shape — `#guard`-able since LoadOps are pure data. ------
--
-- Each segment emits 1–3 ops inside the kernel-picked reservation:
--   • mmapFile (if hasFileBacked) — file overlay (with PROT_WRITE widening)
--   • zeroout  (if hasPartialBss) — clear file content past `filesz`
--   • mprotect — final perms over the whole segment range
--
-- The reservation underneath (kernel-picked anon, RW) handles BSS;
-- no per-segment mmapAnon needed. The single mprotect covers both
-- file overlay and BSS tail since they're all inside the reservation.
--
--   filesz=0          (BSS-only):              [mprotect]                       (1)
--   filesz=memsz      (file-only, aligned):    [mmapFile, mprotect]             (2)
--   file+anon         (file + full-page BSS):  [mmapFile, mprotect]             (2)
--   file+partial      (partial-page BSS):      [mmapFile, zeroout, mprotect]    (3)
--   file+both         (partial + full-page):   [mmapFile, zeroout, mprotect]    (3)
--
-- Tests only inspect the planned ops; they never run the mmap, so a dummy
-- file is enough.
private def dummyHandle : Runtime.File := default

/-- A more general synth helper that lets us vary `filesz` to land in
    each profile. -/
private def synthSeg? (eaddr : Eaddr) (memsz filesz : ByteSize) : Option Segment :=
  let phdr : Parse.ProgramHeader := { (default : Parse.ProgramHeader) with
    p_type := .load,
    p_vaddr := eaddr, p_memsz := memsz,
    p_filesz := filesz, p_offset := 0, p_align := 0x1000 }
  (Segment.ofPhdr phdr exampleFileSize).toOption

private def fileOnlySeg     : Option Segment := synthSeg? 0 0x1000 0x1000  -- file fills page
private def filePartialBss  : Option Segment := synthSeg? 0 0x1000 0x800   -- partial-page BSS only
private def fileAnonBss     : Option Segment := synthSeg? 0 0x2000 0x1000  -- full-page BSS only
private def fileBothBss     : Option Segment := synthSeg? 0 0x2000 0x800   -- partial + full-page

/-- Count of ops (`MmapOp` + `ZeroOp` + `MprotectOp`) `setupSegment` emits
    for one segment. `MmapOp` is 1 if `hasFileBacked`, else 0; `ZeroOp`
    is 1 if `hasPartialBss`, else 0; `MprotectOp` is always 1. -/
private def slotCount (seg : Option Segment) : Option Nat :=
  seg.map fun s =>
    let setup :=
      Exec.setupSegment (SegmentLayout.ofSegmentCore 0 s #[]) dummyHandle exampleAnchor
    (if setup.mmap.isSome then 1 else 0) + (if setup.zero.isSome then 1 else 0) + 1

#guard slotCount bssOnlySeg     = some 1  -- mprotect only
#guard slotCount fileOnlySeg    = some 2  -- mmap + mprotect
#guard slotCount filePartialBss = some 3  -- mmap + zero + mprotect
#guard slotCount fileAnonBss    = some 2  -- mmap + mprotect
#guard slotCount fileBothBss    = some 3  -- mmap + zero + mprotect

-- ---- 4c. Intrinsic safety: vacuously holds for an empty LoadOps. ----------

private def exampleReserve : Reserve :=
  { addr := exampleAnchor, len := 0x1000, noWrap := by decide }

example : Exec.LoadOps exampleReserve.addr exampleReserve.len 0 :=
  { elfs := #[]
    mmapsDisjoint := by
      intro _ _ hi
      simp at hi }

end LeanLoad.Examples

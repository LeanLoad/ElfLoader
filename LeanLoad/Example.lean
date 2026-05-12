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
     base assignment (`Plan/Layout`), and the `SegmentPlan` view
     over a segment (base-free).

  4. **Materialize** — the `Array MemoryOp` derived from a
     `LoadOps` tree that `Main.realize` runs. Shows how
     `Materialize.setupOps` shapes change with BSS-only vs file+BSS
     segments, and how `Materialize.safe` flattens + checks the
     full op list.

`LeanLoad/Test.lean` exercises the real `examples/build/main`
end-to-end; that remains the authoritative "the loader copes with
musl-gcc's actual output" check. This file trades fidelity for
synthesis-driven readability.
-/

import LeanLoad.Plan.Layout
import LeanLoad.Plan.Resolve
import LeanLoad.Materialize.Build
import LeanLoad.Elaborate.Elf

namespace LeanLoad.Example

open LeanLoad
open LeanLoad.Elaborate
open LeanLoad.Plan

-- ============================================================================
-- 1. Test fixtures.
-- ============================================================================

/-- Synthetic reservation base used by examples that don't need a
    real kernel-picked address. Production loads use the address
    returned by `Runtime.mmapAnonAlloc`. -/
private def exampleAnchor : UInt64 := 0x80000000

/-- Default `Elf` — empty in every dimension. Used only by tests that
    synthesize an `Elf` and override the few fields the test cares
    about; production code always goes through `elaborate`. -/
instance : Inhabited Elaborate.Elf where
  default :=
    { elfType := .none, machine := .x86_64,
      entry := 0, phoff := 0, phnum := 0,
      symtab := #[], needed := #[],
      soname := Option.none, runpath := Option.none,
      initArr := #[], finiArr := #[],
      segments := #[],
      segmentsSorted := by decide,
      segmentsNonOverlap := by decide,
      -- `phnum = 0` ⇒ `nbytes = 0`, the vacuous-true branch.
      phdrCovered := Or.inl rfl
      -- Empty init/fini array — vacuously every entry is in some exec seg.
      initArrInExecSeg := by decide
      finiArrInExecSeg := by decide }

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

-- Real-world acceptance: the 127-byte file `third_party/minimal-elf/
-- src/lib.rs::write_elf` emits, with one byte patched (`e_type`
-- 2→3) to make it ET_DYN. minimal-elf itself produces ET_EXEC, which
-- LeanLoad rejects (only PIE / ET_DYN is supported); the patched
-- variant is the smallest ET_DYN binary that exercises the full
-- parse + elaborate path — header + one PT_LOAD phdr + 7 bytes of
-- code, no dynamic / relas / symtab. File layout (gabi 02 § ELF
-- Header, gabi 07 § Program Header):
--
--   [0x00..0x40)  Elf64_Ehdr     (64 bytes)
--   [0x40..0x78)  Elf64_Phdr × 1 (56 bytes, PT_LOAD)
--   [0x78..0x7f)  program code   (7 bytes, the e_entry target)
private def minimalElfBytes : ByteArray := ⟨#[
  -- ── e_ident (16 bytes, gabi 02 § ELF Identification) ───────────────────
  0x7f, 0x45, 0x4c, 0x46,           -- [0x00] EI_MAG0..3  = "\x7fELF" magic
  0x02,                             -- [0x04] EI_CLASS    = ELFCLASS64 (64-bit)
  0x01,                             -- [0x05] EI_DATA     = ELFDATA2LSB (little-endian)
  0x01,                             -- [0x06] EI_VERSION  = EV_CURRENT
  0x00,                             -- [0x07] EI_OSABI    = ELFOSABI_NONE (System V)
  0x00,                             -- [0x08] EI_ABIVERSION = 0
  0x00, 0x00, 0x00,                 -- [0x09] EI_PAD (7 reserved bytes, must be zero)
  0x00, 0x00, 0x00, 0x00,           -- [0x0c]   …continued
  -- ── rest of Elf64_Ehdr (48 bytes) ──────────────────────────────────────
  0x03, 0x00,                                       -- [0x10] e_type      = ET_DYN (3; minimal-elf emits 2=ET_EXEC, patched here)
  0x3e, 0x00,                                       -- [0x12] e_machine   = EM_X86_64 (0x3e = 62)
  0x01, 0x00, 0x00, 0x00,                           -- [0x14] e_version   = EV_CURRENT (1)
  0x78, 0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00,   -- [0x18] e_entry     = 0x400078 (VADDR 0x400000 + 120-byte hdr prefix)
  0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- [0x20] e_phoff     = 64 (phdr table starts right after ehdr)
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- [0x28] e_shoff     = 0 (no section headers — stripped)
  0x00, 0x00, 0x00, 0x00,                           -- [0x30] e_flags     = 0 (no processor-specific flags)
  0x40, 0x00,                                       -- [0x34] e_ehsize    = 64 (size of this header)
  0x38, 0x00,                                       -- [0x36] e_phentsize = 56 (size of one phdr)
  0x01, 0x00,                                       -- [0x38] e_phnum     = 1 (single PT_LOAD)
  0x00, 0x00,                                       -- [0x3a] e_shentsize = 0
  0x00, 0x00,                                       -- [0x3c] e_shnum     = 0
  0x00, 0x00,                                       -- [0x3e] e_shstrndx  = 0
  -- ── Elf64_Phdr (56 bytes, at file offset 64) ───────────────────────────
  0x01, 0x00, 0x00, 0x00,                           -- [0x40] p_type   = PT_LOAD (1)
  0x07, 0x00, 0x00, 0x00,                           -- [0x44] p_flags  = PF_R|PF_W|PF_X (1|2|4 = 7); RWX in one page
  0x78, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- [0x48] p_offset = 120 (code begins right after ehdr+phdr)
  0x78, 0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00,   -- [0x50] p_vaddr  = 0x400078 (matches e_entry; gabi-07: p_vaddr ≡ p_offset mod p_align)
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- [0x58] p_paddr  = 0 (unused on Linux)
  0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- [0x60] p_filesz = 7 (file bytes for this segment)
  0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- [0x68] p_memsz  = 7 (mem bytes; filesz==memsz means no BSS tail)
  0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- [0x70] p_align  = 0x1000 (4 KiB page)
  -- ── program (7 bytes, at file offset 120, the e_entry target) ──────────
  -- Linux x86-64 exit(0) trampoline. Encoded via `push imm8 / pop %rax`
  -- (3 bytes) which is shorter than `mov $60, %eax` (5 bytes).
  0x6a, 0x3c,                       -- [0x78] push  $0x3c     (60 = SYS_exit on Linux x86-64)
  0x58,                             -- [0x7a] pop   %rax      (%rax := SYS_exit)
  0x31, 0xff,                       -- [0x7b] xor   %edi, %edi (status := 0; argv[0] of exit())
  0x0f, 0x05                        -- [0x7d] syscall          (→ exit(0); never returns)
]⟩

#guard minimalElfBytes.size == 127  -- = 0x7f; 64 ehdr + 56 phdr + 7 code

private def parsedMinimalElf : Option (Parse.RawEhdr × Parse.RawPhdr) :=
  let p : Parse.Parser (Parse.RawEhdr × Parse.RawPhdr) := do
    let h ← (Parse.BytesDecode.decode : Parse.Parser Parse.RawEhdr)
    let ph ← (Parse.BytesDecode.decode : Parse.Parser Parse.RawPhdr)
    return (h, ph)
  (Parse.Parser.run minimalElfBytes p).toOption

#guard (parsedMinimalElf.map (·.1.e_type))            == some 3   -- ET_DYN
#guard (parsedMinimalElf.map (·.1.e_machine))         == some 62  -- EM_X86_64
#guard (parsedMinimalElf.map (·.1.e_entry))           == some 0x400078
#guard (parsedMinimalElf.map (·.1.ident.ei_class))    == some ELFCLASS64
#guard (parsedMinimalElf.map (·.1.ident.ei_data))     == some ELFDATA2LSB
#guard (parsedMinimalElf.map (·.2.p_type))            == some Parse.PT_LOAD
#guard (parsedMinimalElf.map (·.2.p_vaddr))           == some 0x400078
#guard (parsedMinimalElf.map (·.2.p_memsz))           == some 7

/-- Reassemble a `RawElf` from the parsed header + single phdr (the
    binary has no dynamic section, no relas, no symtab — it's static
    and libc-free). With `e_type = ET_DYN`, `elaborate` accepts: the
    per-segment gabi-07 checks succeed and every header invariant
    holds. -/
private def minimalRawElf : Option Parse.RawElf :=
  parsedMinimalElf.map fun (h, ph) =>
    { (default : Parse.RawElf) with header := h, phdrs := #[ph] }

#guard match minimalRawElf.map elaborate with
       | some (.ok elf) =>
           elf.elfType    == .dyn
        && elf.machine    == .x86_64
        && elf.entry      == 0x400078
        && elf.segments.size == 1
       | _ => false

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

-- ET_EXEC is rejected at elaborate time, so every elf reaching
-- planning is ET_DYN. `assignBases` takes the reservation base
-- as a parameter; production gets it from `Runtime.mmapAnon`.
#guard
  let elfs : Array Elaborate.Elf := #[synthElf (elfType := .dyn)]
  let rt := Resolve.buildTable elfs
  match LoadPlan.ofElfs elfs rt with
  | .ok lp => assignBases exampleAnchor lp == #[exampleAnchor]
  | .error _ => false

-- A single-segment array's `Sorted` and `NonOverlap` predicates are
-- vacuously true (no `i < j` with both `< 1`). Provide explicit
-- proofs since `synthElf`'s `by decide` defaults can't discharge a
-- type containing a free `Segment` variable.
private theorem sorted_singleton (seg : Segment) :
    Elaborate.Sorted #[seg] := by
  intro i hi j hj h_ij
  simp at hi hj
  omega

private theorem nonOverlap_singleton (seg : Segment) :
    Elaborate.NonOverlap #[seg] := by
  intro i hi j hj h_ij
  simp at hi hj
  omega

-- Stacking: each `.dyn` lib has a 0x2000-byte span (one PT_LOAD at
-- vaddr 0 of memsz 0x2000 → pageEndAddr 0x2000), `advance =
-- alignUp 0x2000 0x1000 = 0x2000`. So three libs get
-- exampleAnchor, exampleAnchor + 0x2000, exampleAnchor + 0x4000.
private def stackingExample : Option (Array UInt64) := do
  let seg ← synthSegment? 0 0x2000
  let libElf := synthElf (elfType := .dyn) (segments := #[seg])
                  (segmentsSorted := sorted_singleton seg)
                  (segmentsNonOverlap := nonOverlap_singleton seg)
  let elfs := #[libElf, libElf, libElf]
  let rt := Resolve.buildTable elfs
  match LoadPlan.ofElfs elfs rt with
  | .ok lp => some (assignBases exampleAnchor lp)
  | .error _ => none

#guard stackingExample = some #[exampleAnchor, exampleAnchor + 0x2000, exampleAnchor + 0x4000]

-- ============================================================================
-- 4. Realize plan: `SegmentPlan` views and `Array MemoryOp` shapes.
--
-- `SegmentPlan` is the base-free loader view of a segment; absolute
-- addresses come from `base + sp.pageVaddr` at materialize time.
-- ============================================================================

-- ---- 4a. SegmentPlan view: base-free page math. ----------------------------

/-- A 0x2000-byte BSS-only segment at vaddr 0 (page-aligned). With
    `filesz = 0` and `memsz = 0x2000`, this is two pages of pure BSS
    with no file backing. -/
private def bssOnlySeg : Option Segment :=
  let phdr : Parse.RawPhdr := { (default : Parse.RawPhdr) with
    p_type := Parse.PT_LOAD,
    p_vaddr := 0, p_memsz := 0x2000,
    p_filesz := 0, p_offset := 0, p_align := 0x1000 }
  (Segment.ofPhdr phdr #[] #[]).toOption

private def bssOnlyPlan : Option (SegmentPlan 0) :=
  bssOnlySeg.map (fun s => SegmentPlan.ofSegmentCore 0 s #[])

-- The plan's mmap'd range is `[pageVaddr, pageVaddr + pageLength)`,
-- absolute addresses computed as `base + pageVaddr`.
#guard bssOnlyPlan.map (·.pageVaddr)   = some 0
#guard bssOnlyPlan.map (·.pageLength)  = some 0x2000

-- BSS-only: no file backing — the underlying object reservation
-- already covers it (kernel zero-fills MAP_ANONYMOUS).
#guard bssOnlyPlan.map (·.hasFileBacked) = some false

-- ---- 4b. setupOps shape — `#guard`-able since `MemoryOp` is pure. ---------
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
-- `FileHandle` is just a `UInt32` (transparent), so tests construct
-- one with any number; the kernel rejects invalid fds at the syscall.
private def dummyHandle : Runtime.FileHandle := 0

/-- A more general synth helper that lets us vary `filesz` to land in
    each profile. -/
private def synthSeg? (vaddr memsz filesz : UInt64) : Option Segment :=
  let phdr : Parse.RawPhdr := { (default : Parse.RawPhdr) with
    p_type := Parse.PT_LOAD,
    p_vaddr := vaddr, p_memsz := memsz,
    p_filesz := filesz, p_offset := 0, p_align := 0x1000 }
  (Segment.ofPhdr phdr #[] #[]).toOption

private def fileOnlySeg     : Option Segment := synthSeg? 0 0x1000 0x1000  -- file fills page
private def filePartialBss  : Option Segment := synthSeg? 0 0x1000 0x800   -- partial-page BSS only
private def fileAnonBss     : Option Segment := synthSeg? 0 0x2000 0x1000  -- full-page BSS only
private def fileBothBss     : Option Segment := synthSeg? 0 0x2000 0x800   -- partial + full-page

/-- Count of slots (`Mmap` + `Zero` + `Mprotect`) `setupSlots` emits
    for one segment. `Mmap` is 1 if `hasFileBacked`, else 0; `Zero`
    is 1 if `hasPartialBss`, else 0; `Mprotect` is always 1. -/
private def slotCount (seg : Option Segment) : Option Nat :=
  seg.map fun s =>
    let (mmap, zero, _mp) :=
      Materialize.setupSlots (SegmentPlan.ofSegmentCore 0 s #[]) dummyHandle exampleAnchor
    (if mmap.isSome then 1 else 0) + (if zero.isSome then 1 else 0) + 1

#guard slotCount bssOnlySeg     = some 1  -- mprotect only
#guard slotCount fileOnlySeg    = some 2  -- mmap + mprotect
#guard slotCount filePartialBss = some 3  -- mmap + zero + mprotect
#guard slotCount fileAnonBss    = some 2  -- mmap + mprotect
#guard slotCount fileBothBss    = some 3  -- mmap + zero + mprotect

-- ---- 4c. Safety predicates: vacuously hold for an empty LoadOps. ----------
--
-- The five `MmapsDisjoint` / `*Contained` predicates that
-- `Materialize.build` discharges are decidable, so we can probe them
-- directly on a synthetic empty load tree. With no slots, all five
-- predicates hold for any reservation by vacuous quantification.

private def exampleReserve : Reserve :=
  { addr := exampleAnchor, len := 0x1000, noWrap := by decide }

#guard decide (Materialize.MmapsDisjoint (n := 0) #[]) = true
#guard decide
    (Materialize.MmapsContained exampleReserve.addr exampleReserve.len (n := 0) #[]) = true
#guard decide
    (Materialize.ZerosContained exampleReserve.addr exampleReserve.len (n := 0) #[]) = true
#guard decide
    (Materialize.StoresContained exampleReserve.addr exampleReserve.len (n := 0) #[]) = true
#guard decide
    (Materialize.MprotectsContained exampleReserve.addr exampleReserve.len (n := 0) #[]) = true
-- The five predicates bundled into one Prop; same vacuous truth.
#guard decide
    (Materialize.Safe exampleReserve.addr exampleReserve.len (n := 0) #[]) = true

end LeanLoad.Example

/-
ELF elaboration — pure stage between byte decoding (`Parse`) and the
planner.

Takes a `Parse.RawElf` (bytes-decoded only, no semantic checks) and
returns an `Elaborate.Elf`:

  - 64-bit / little-endian sanity checks on the header (`ELFCLASS64`,
    `ELFDATA2LSB`) — these used to live in `Parse.Header.parse`,
    now consolidated here so `Parse` is byte-blind.
  - PT_LOAD well-formedness (`Elaborate.WellFormedB`).
  - Every `DT_RELA` / `DT_JMPREL` entry located against a covering
    PT_LOAD segment, witnessed by the subtype on
    `Elaborate.Segment.{rela, jmprel}`.
  - Per-segment relocation grouping built into `Array Elaborate.Segment`.
  - Symbol names pre-resolved against the dynamic string table.

Symbol classification predicates (`isGlobalDef`, `isUndef`, `isWeak`)
are also defined in this file — on `Parse.RawSym` for dot notation,
using the `STB_*`/`SHN_*` constants below.

Failures are `Except String`: malformed ELF class/endianness,
malformed PT_LOAD shape, or any rela whose write window doesn't fit
a PT_LOAD.
-/

import LeanLoad.Parse.File
import LeanLoad.Elaborate.Segment

-- ============================================================================
-- Semantic constants. Live here (not in Parse) because Parse is
-- meant to be semantics-blind. Used by `elaborate` for ELF class /
-- endian checks, and by the symbol predicates below.
-- ============================================================================

namespace LeanLoad.Elaborate

-- ELF identification (gabi 02)
def ELFCLASS64  : UInt8 := 2
def ELFDATA2LSB : UInt8 := 1

-- e_type (gabi 02 Table: Object File Types)
def ET_NONE : UInt16 := 0
def ET_REL  : UInt16 := 1
def ET_EXEC : UInt16 := 2
def ET_DYN  : UInt16 := 3
def ET_CORE : UInt16 := 4

-- st_info high nibble (binding) — gabi 05
def STB_LOCAL  : UInt8 := 0
def STB_GLOBAL : UInt8 := 1
def STB_WEAK   : UInt8 := 2

-- st_info low nibble (type) — gabi 05
def STT_NOTYPE  : UInt8 := 0
def STT_OBJECT  : UInt8 := 1
def STT_FUNC    : UInt8 := 2
def STT_SECTION : UInt8 := 3
def STT_FILE    : UInt8 := 4
def STT_COMMON  : UInt8 := 5
def STT_TLS     : UInt8 := 6

-- Reserved section indices — gabi 05
def SHN_UNDEF  : UInt16 := 0
def SHN_ABS    : UInt16 := 0xfff1
def SHN_COMMON : UInt16 := 0xfff2

end LeanLoad.Elaborate

-- ============================================================================
-- Symbol classification predicates. Defined in `Parse.RawSym`'s
-- namespace so dot notation (`sym.isGlobalDef`) resolves; the logic
-- is morally Elaborate (semantic interpretation of bit fields).
-- ============================================================================

namespace LeanLoad.Parse.RawSym

open LeanLoad.Elaborate (STB_LOCAL STB_WEAK SHN_UNDEF)

/-- True iff `sym` is an externally-visible definition. -/
def isGlobalDef (s : RawSym) : Bool :=
  s.st_shndx != SHN_UNDEF && s.bind != STB_LOCAL

/-- True iff `sym` is an undefined reference. -/
def isUndef (s : RawSym) : Bool :=
  s.st_shndx == SHN_UNDEF

/-- True iff `sym` is weak (gabi 05): a weak undefined reference is
    allowed to remain unresolved at link time. -/
def isWeak (s : RawSym) : Bool :=
  s.bind == STB_WEAK

end LeanLoad.Parse.RawSym

namespace LeanLoad.Elaborate

open LeanLoad
open LeanLoad.Parse (RawElf RawPhdr RawRela RawSym)

-- ============================================================================
-- Per-symbol bundle: a `RawSym` paired with its pre-resolved name.
-- ============================================================================

/-- A `RawSym` plus its pre-resolved name. `none` if the entry's
    `st_name` offset doesn't point into the string table. -/
structure Symbol where
  sym  : RawSym
  name : Option String
  deriving Inhabited

-- ============================================================================
-- The elaborated ELF.
-- ============================================================================

/-- The elaborated form of an ELF.

    `elaborate` (below) enforces ELF-class / endian sanity, gabi-07
    PT_LOAD well-formedness, and per-rela segment containment as
    preconditions on construction; the `Elf` type *is* the witness
    that those checks passed.

    Fields dropped from `RawElf`: `phdrs` (replaced by
    `segments.map (·.phdr)`), `dyn` (no post-parse consumer),
    `strtab` (consumed at elaboration time to pre-resolve symbol and
    DT_NEEDED names; no remaining downstream consumer). -/
structure Elf where
  header   : Parse.RawEhdr
  symtab   : Array Symbol
  needed   : Array String
  soname   : Option String
  runpath  : Option String
  initArr  : Array UInt64
  /-- One bundle per PT_LOAD, in phdr order, with relas grouped by
      the segment they target. -/
  segments : Array Segment
  deriving Inhabited

namespace Elf

/-- The PT_LOAD phdrs, in order. Convenience for consumers that only
    need the underlying `RawPhdr`s. -/
def loadablePhdrs (e : Elf) : Array RawPhdr :=
  e.segments.map (·.phdr)

end Elf

-- ============================================================================
-- elaborate: RawElf → Except String Elf
-- ============================================================================

/-- Find the PT_LOAD index that fully covers `r`'s 8-byte write
    window, with its containment witness. Returns `none` if no
    segment covers the write range. -/
private def locateRela (segs : Array RawPhdr) (r : RawRela) :
    Option (Σ' (i : Fin segs.size), segs[i].containsRela r) := Id.run do
  for h : i in [:segs.size] do
    let s := segs[i]
    if h_lo : s.p_vaddr.toNat ≤ r.r_offset.toNat then
      if h_hi : r.r_offset.toNat + 8 ≤ s.p_vaddr.toNat + s.p_memsz.toNat then
        return some ⟨⟨i, h.upper⟩, h_lo, h_hi⟩
  return none

/-- Elaborate a `RawElf`: check ELF class/endian, PT_LOAD
    well-formedness, locate every rela against a segment, bundle
    into `Array Segment`, pre-resolve every symbol's name. -/
def elaborate (raw : RawElf) : Except String Elf := do
  if raw.header.ident.ei_class != ELFCLASS64 then
    .error s!"elaborate: only ELFCLASS64 supported \
      (got ei_class={raw.header.ident.ei_class})"
  if raw.header.ident.ei_data != ELFDATA2LSB then
    .error s!"elaborate: only little-endian supported \
      (got ei_data={raw.header.ident.ei_data})"
  let loadable := fromPhdrs raw.phdrs
  if WellFormedB loadable = false then
    .error "elaborate: malformed PT_LOAD segments \
      (gabi-07 mandates: sort by p_vaddr, p_filesz ≤ p_memsz, p_align \
      is a power of 2, p_vaddr ≡ p_offset mod p_align; non-overlap is \
      de facto from linker)"
  -- Per-rela "tagged with its segment index" (Sigma — destructurable).
  let GEntry := Σ i : Fin loadable.size, { r : RawRela // loadable[i].containsRela r }
  let groupOne (label : String) (rs : Array RawRela) :
      Except String (Array (Array GEntry)) := do
    let mut buckets : Array (Array GEntry) := Array.replicate loadable.size #[]
    for r in rs do
      match locateRela loadable r with
      | none =>
        .error s!"elaborate {label}: rela r_offset=0x{r.r_offset.toNat} \
          not covered by any PT_LOAD segment"
      | some ⟨i, h_in⟩ =>
        let entry : GEntry := ⟨i, ⟨r, h_in⟩⟩
        buckets := buckets.modify i.val (·.push entry)
    return buckets
  let relaBuckets   ← groupOne "DT_RELA"   raw.rela
  let jmprelBuckets ← groupOne "DT_JMPREL" raw.jmprel
  let buildBucket (bucketIdx : Fin loadable.size) (bucket : Array GEntry) :
      Array { r : RawRela // loadable[bucketIdx].containsRela r } :=
    bucket.filterMap fun ⟨i, ⟨r, h_in⟩⟩ =>
      if h_eq : i = bucketIdx then some ⟨r, h_eq ▸ h_in⟩
      else none
  -- Each loadable phdr is PT_LOAD by construction (`fromPhdrs` filtered);
  -- recover the witness per-segment.
  let segments : Array Segment := Id.run do
    let mut acc : Array Segment := #[]
    for h : i in [:loadable.size] do
      let bucketIdx : Fin loadable.size := ⟨i, h.upper⟩
      let phdr := loadable[bucketIdx]
      let isLoad : phdr.p_type = Parse.PT_LOAD := by
        have h_mem : phdr ∈ loadable := Array.getElem_mem h.upper
        have hf := Array.mem_filter.mp h_mem
        exact (beq_iff_eq).mp hf.2
      let rB := relaBuckets[i]?.getD #[]
      let jB := jmprelBuckets[i]?.getD #[]
      acc := acc.push
        { phdr, isLoad,
          rela   := buildBucket bucketIdx rB
          jmprel := buildBucket bucketIdx jB }
    return acc
  let symtab : Array Symbol := raw.symtab.map fun sym =>
    { sym, name := Parse.RawStrtab.lookup raw.strtab sym.st_name.toNat }
  return {
    header := raw.header, symtab,
    needed := raw.needed, soname := raw.soname, runpath := raw.runpath,
    initArr := raw.initArr, segments
  }

end LeanLoad.Elaborate

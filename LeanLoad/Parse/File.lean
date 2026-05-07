/-
Aggregate ELF parser: walks an entire ELF the way a loader needs to —
header → program headers → `.dynamic` → string table → dynamic symbol
table → relocation tables → `DT_NEEDED` strings → init/fini lists.

The dynamic symbol-table count is taken from `DT_HASH`'s `nchain`
field (gabi 08 § Hash Table) when present, falling back to walking
`DT_GNU_HASH`'s chain table when only the GNU extension is emitted
(gnu-gabi `program-loading-and-dynamic-linking.txt` § Hashes). Modern
Linux toolchains default to gnu-only.

Spec types live in `LeanLoad.Spec.{Header,Program,Dynamic,Symbol,Reloc}`;
this file just glues their parsers together into a `ParsedElf`.
-/

import LeanLoad.Parse.Bytes
import LeanLoad.Parse.Header
import LeanLoad.Parse.Program
import LeanLoad.Parse.Dynamic
import LeanLoad.Parse.StringTable
import LeanLoad.Parse.Symbol
import LeanLoad.Parse.Reloc
import LeanLoad.Parse.GnuHash
import LeanLoad.Parse.Segment
import LeanLoad.Runtime

namespace LeanLoad.Parse.File

open LeanLoad
open LeanLoad.Parse.Bytes

-- ============================================================================
-- Virtual-address ↔ file-offset translation
-- ============================================================================

/-- Witness packaged with `vaToOffset`'s `some` branch: there is a
    `PT_LOAD` `ph ∈ phdrs` whose virtual range covers `va` and `off`
    is its file-offset translation. The witness used to live as a
    separate theorem (`Thm.vaToOffset_correct`); now it's in the
    return type and consumers that need the proof get it for free. -/
abbrev VaToOffsetSpec (phdrs : Array Spec.Program.Header64) (va : UInt64) (off : Nat) : Prop :=
  ∃ ph ∈ phdrs,
    ph.p_type = Spec.Program.PT_LOAD ∧
    ph.p_vaddr ≤ va ∧
    va < ph.p_vaddr + ph.p_memsz ∧
    off = (va - ph.p_vaddr).toNat + ph.p_offset.toNat

/-- Translate a virtual address to a file offset by walking the
    `PT_LOAD` segments. Returns `none` if no `PT_LOAD` covers the
    address; the `some` branch carries `VaToOffsetSpec` as a
    structural witness. -/
def vaToOffset (phdrs : Array Spec.Program.Header64) (va : UInt64) :
    Option { off : Nat // VaToOffsetSpec phdrs va off } := Id.run do
  for h : i in [:phdrs.size] do
    let ph := phdrs[i]
    if h_load : ph.p_type = Spec.Program.PT_LOAD then
      if h_lo : ph.p_vaddr ≤ va then
        if h_hi : va < ph.p_vaddr + ph.p_memsz then
          let off := (va - ph.p_vaddr).toNat + ph.p_offset.toNat
          have h_mem : ph ∈ phdrs := phdrs.getElem_mem h.upper
          return some ⟨off, ⟨ph, h_mem, h_load, h_lo, h_hi, rfl⟩⟩
  return none

section Example
-- A two-segment ELF: [.text @va 0x1000, file 0x1000, len 0x1000]
-- and [.data @va 0x3000, file 0x2000, len 0x500]. The witness in
-- `vaToOffset`'s return type is structural — these `#guard`s are
-- input→output examples for the reader, so we elide the witness via
-- a private wrapper to keep each line a single equation.
private def phdrs : Array Spec.Program.Header64 := #[
  { (default : Spec.Program.Header64) with
    p_type := Spec.Program.PT_LOAD,
    p_vaddr := 0x1000, p_memsz := 0x1000,
    p_offset := 0x1000, p_filesz := 0x1000 },
  { (default : Spec.Program.Header64) with
    p_type := Spec.Program.PT_LOAD,
    p_vaddr := 0x3000, p_memsz := 0x500,
    p_offset := 0x2000, p_filesz := 0x500 } ]

/-- Just the offset, witness elided. Used only by the `#guard`
    examples below so they read as a clean input→output table. -/
private def vaToOffsetNat (phdrs : Array Spec.Program.Header64) (va : UInt64) : Option Nat :=
  (vaToOffset phdrs va).map (·.val)

#guard vaToOffsetNat phdrs 0x1000 = some 0x1000   -- start of .text
#guard vaToOffsetNat phdrs 0x1abc = some 0x1abc   -- mid .text
#guard vaToOffsetNat phdrs 0x3010 = some 0x2010   -- mid .data (different file offset)
#guard vaToOffsetNat phdrs 0x0fff = none           -- before .text
#guard vaToOffsetNat phdrs 0x2500 = none           -- gap between segments
#guard vaToOffsetNat phdrs 0x3500 = none           -- past .data
end Example

-- ============================================================================
-- Aggregated parse result (project-defined; not gabi)
-- ============================================================================

/-- Everything the loader needs that comes from parsing a single ELF. -/
structure ParsedElf where
  header  : Spec.Header.ElfHeader64
  phdrs   : Array Spec.Program.Header64
  /-- The `.dynamic` array, empty if no `PT_DYNAMIC`. -/
  dyn     : Array Spec.Dynamic.Dyn64
  /-- The dynamic string table (`DT_STRTAB`), empty if absent. -/
  strtab  : Spec.StringTable.StringTable
  /-- Dynamic symbol table (`DT_SYMTAB`), sized via `DT_HASH`'s
      `nchain`. Empty if neither is present. -/
  symtab  : Array Spec.Symbol.Symbol64
  /-- Resolved `DT_NEEDED` strings, in dynamic-array order. -/
  needed  : Array String
  /-- `DT_SONAME` if present (the canonical name of this object). -/
  soname  : Option String
  /-- `DT_RUNPATH` (gabi 08; deprecated `DT_RPATH` falls back to this). -/
  runpath : Option String
  /-- General `Rela` relocations from `DT_RELA`. -/
  rela    : Array Spec.Reloc.Rela64
  /-- PLT relocations from `DT_JMPREL` (only `Rela` form supported). -/
  jmprel  : Array Spec.Reloc.Rela64
  /-- `DT_INIT_ARRAY` entries — already parsed from the file bytes. For
      `ET_DYN`, each entry is a relative address; the runtime adds the
      chosen base. For `ET_EXEC`, entries are absolute. (gabi 08 also
      defines `DT_INIT`, `DT_FINI`, `DT_FINI_ARRAY`, `DT_PREINIT_ARRAY`;
      none are consumed by the loader yet — added back when needed.) -/
  initArr : Array UInt64
  deriving Inhabited

-- ============================================================================
-- Helpers for reading from a `.dynamic` array
-- ============================================================================

private def dynVal? (dyn : Array Spec.Dynamic.Dyn64) (tag : UInt64) : Option UInt64 :=
  (Parse.Dynamic.find? dyn tag).map (·.d_un)

private def dynPair? (dyn : Array Spec.Dynamic.Dyn64) (tagA tagB : UInt64) : Option (UInt64 × UInt64) := do
  let a ← dynVal? dyn tagA
  let b ← dynVal? dyn tagB
  return (a, b)

/-- Find the `PT_LOAD` whose file range covers `off`. Used to upper-
    bound `DT_GNU_HASH`'s chain (no size field in the dynamic table). -/
private def containingPTLoad (phdrs : Array Spec.Program.Header64) (off : Nat)
    : Option Spec.Program.Header64 :=
  phdrs.find? fun ph =>
    ph.p_type == Spec.Program.PT_LOAD &&
    ph.p_offset.toNat ≤ off &&
    off < ph.p_offset.toNat + ph.p_filesz.toNat

/-- `pread` `len` bytes at `offset` (via the runtime capability) and
    run `parser` from the start. Each section's parsers take an
    `offset` parameter that becomes 0 here (we already preadʼd from
    the file at the right place). -/
private def parseSection {α} (rt : Runtime.Ops) (h : Runtime.FileHandle)
    (label : String) (offset : UInt64) (len : USize) (parser : Parser α) : IO α := do
  let bytes ← rt.pread h offset len
  match Parser.run bytes parser with
  | .ok v    => pure v
  | .error e => throw (IO.userError s!"parse {label}: {e}")

/-- Resolve `vaddr` to a file offset; throw if no `PT_LOAD` covers it.
    Discards the witness (callers downstream don't need it; it stays
    available via `vaToOffset` directly when proofs do). -/
private def vaToOffsetIO (phdrs : Array Spec.Program.Header64) (label : String)
    (vaddr : UInt64) : IO Nat :=
  match vaToOffset phdrs vaddr with
  | some ⟨off, _⟩ => pure off
  | none          => throw (IO.userError s!"parse {label}: va 0x{vaddr.toNat} not in any PT_LOAD")

-- ============================================================================
-- Top-level parser — `pread`-driven, one section per syscall.
-- ============================================================================

/-- Parse an ELF file via per-section `pread`s on a `FileHandle`.
    Each section's bytes live in their own small `ByteArray` and are
    GC'd after parsing — no whole-file `ByteArray` is constructed.

    This is the *raw* parser: it returns a `ParsedElf` without
    validating PT_LOAD well-formedness. The structural checks
    (`Parse.Segment.WellFormedB`) are pure and run separately via
    `validate`; callers that want both compose `parse` then
    `validate`. The split keeps I/O failure (short reads, missing
    sections) distinct from validation failure (well-formed bytes
    that nevertheless violate gabi-07 / linker conventions). -/
def parse (rt : Runtime.Ops) (h : Runtime.FileHandle) : IO ParsedElf := do
  -- ELF header (64 bytes).
  -- ELF header is fixed-size (gabi 02 Elf64_Ehdr: 64 bytes).
  let header ← parseSection rt h "header" 0 64 Parse.Header.parse

  -- Phdr table (e_phnum × 56 bytes).
  let phdrTableSize := (header.e_phnum.toNat * Spec.Program.entrySize).toUSize
  let phdrs ← parseSection rt h "phdrs" header.e_phoff phdrTableSize
                (Parse.Program.parseTable 0 header.e_phnum.toNat)

  -- PT_DYNAMIC (sized by `p_filesz`).
  let dyn ← match phdrs.find? (·.p_type == Spec.Program.PT_DYNAMIC) with
    | none    => pure #[]
    | some ph =>
      parseSection rt h "dynamic" ph.p_offset ph.p_filesz.toNat.toUSize
        (Parse.Dynamic.parseTable 0 ph.p_filesz.toNat)

  -- DT_STRTAB (sized by DT_STRSZ).
  let strtab ← match dynPair? dyn Spec.Dynamic.DT_STRTAB Spec.Dynamic.DT_STRSZ with
    | none             => pure (ByteArray.mk #[])
    | some (vaddr, sz) =>
      let off ← vaToOffsetIO phdrs "DT_STRTAB" vaddr
      parseSection rt h "DT_STRTAB" off.toUInt64 sz.toNat.toUSize
        (Parse.StringTable.parse 0 sz.toNat)

  -- Symbol count (from DT_HASH's nchain or by walking DT_GNU_HASH's chain).
  let symCount : Nat ←
    match dynVal? dyn Spec.Dynamic.DT_HASH, dynVal? dyn Spec.Dynamic.DT_GNU_HASH with
    | some hashVa, _ =>
      let off ← vaToOffsetIO phdrs "DT_HASH" hashVa
      -- Need only the 8-byte (nbucket, nchain) header.
      parseSection rt h "DT_HASH" off.toUInt64 8
        (do let _ ← Bytes.u32le; let nchain ← Bytes.u32le; return nchain.toNat)
    | none, some gnuHashVa =>
      let off ← vaToOffsetIO phdrs "DT_GNU_HASH" gnuHashVa
      -- Chain extends until end of containing PT_LOAD; pread that tail.
      match containingPTLoad phdrs off with
      | none    => throw (IO.userError s!"parse DT_GNU_HASH: offset 0x{off} in no PT_LOAD")
      | some ph =>
        let segEnd  := ph.p_offset.toNat + ph.p_filesz.toNat
        let availLen := (segEnd - off).toUSize
        parseSection rt h "DT_GNU_HASH" off.toUInt64 availLen
          (Parse.GnuHash.parseSymCount 0)
    | none, none => pure 0

  -- DT_SYMTAB (sized by `symCount × Symbol64.entrySize`).
  let symtab ← if symCount == 0 then pure #[]
    else match dynVal? dyn Spec.Dynamic.DT_SYMTAB with
      | none       => pure #[]
      | some vaddr =>
        let off := ← vaToOffsetIO phdrs "DT_SYMTAB" vaddr
        let symSize := (symCount * Spec.Symbol.entrySize).toUSize
        parseSection rt h "DT_SYMTAB" off.toUInt64 symSize
          (Parse.Symbol.parseTable 0 symCount)

  let neededOffsets := (Parse.Dynamic.findAll dyn Spec.Dynamic.DT_NEEDED).map (·.d_un)
  let needed := neededOffsets.filterMap (fun off => Spec.StringTable.lookup strtab off.toNat)

  let lookupStr (tag : UInt64) : Option String :=
    (dynVal? dyn tag).bind (fun off => Spec.StringTable.lookup strtab off.toNat)
  let soname  := lookupStr Spec.Dynamic.DT_SONAME
  let runpath := lookupStr Spec.Dynamic.DT_RUNPATH <|> lookupStr Spec.Dynamic.DT_RPATH

  -- DT_RELA / DT_JMPREL (sized by their respective `*SZ`).
  let parseRelaPair (tagAddr tagSz : UInt64) (label : String) : IO (Array Spec.Reloc.Rela64) := do
    match dynPair? dyn tagAddr tagSz with
    | none             => pure #[]
    | some (vaddr, sz) =>
      let off ← vaToOffsetIO phdrs label vaddr
      let count := sz.toNat / Spec.Reloc.Rela64.entrySize
      parseSection rt h label off.toUInt64 sz.toNat.toUSize
        (Parse.Reloc.parseRelaTable 0 count)
  let rela   ← parseRelaPair Spec.Dynamic.DT_RELA   Spec.Dynamic.DT_RELASZ   "DT_RELA"
  let jmprel ← parseRelaPair Spec.Dynamic.DT_JMPREL Spec.Dynamic.DT_PLTRELSZ "DT_JMPREL"

  -- DT_INIT_ARRAY (sized by DT_INIT_ARRAYSZ).
  let initArr ← match dynPair? dyn Spec.Dynamic.DT_INIT_ARRAY Spec.Dynamic.DT_INIT_ARRAYSZ with
    | none             => pure #[]
    | some (vaddr, sz) =>
      let off ← vaToOffsetIO phdrs "DT_INIT_ARRAY" vaddr
      let count := sz.toNat / 8
      parseSection rt h "DT_INIT_ARRAY" off.toUInt64 sz.toNat.toUSize
        (Bytes.parseArray 0 count Bytes.u64le)

  return {
    header, phdrs, dyn, strtab, symtab, needed, soname, runpath,
    rela, jmprel, initArr
  }

/-- Convenience: extract loadable segments from a parsed ELF. -/
def segmentsOf (elf : ParsedElf) : Array Spec.Program.Segment :=
  Parse.Segment.fromPhdrs elf.phdrs

/-- Pure parse-time validation: check the PT_LOAD well-formedness
    invariant (sortedness, file/mem sizing, alignment, gabi-07
    congruence, raw non-overlap) and return the parsed ELF together
    with the witness on success.

    All five clauses are properties of header bytes only — no I/O —
    so this is `Except`-valued, separate from `parse`'s `IO`. The
    boundary between "well-formed bytes but malformed structure" and
    "I/O failure / unparseable bytes" is now type-level: the former
    becomes a structured `Except` error, the latter stays an
    `IO.userError`. Compose via `parse h >>= IO.ofExcept ∘ validate`
    to get the witnessed subtype back. -/
def validate (elf : ParsedElf) :
    Except String
      { e : ParsedElf // Parse.Segment.WellFormed (Parse.Segment.fromPhdrs e.phdrs) } :=
  if h : Parse.Segment.WellFormedB (Parse.Segment.fromPhdrs elf.phdrs) = true then
    .ok ⟨elf, h⟩
  else
    .error "validate: malformed PT_LOAD segments \
      (gabi-07 mandates: sort by p_vaddr, p_filesz ≤ p_memsz, p_align \
      is a power of 2, p_vaddr ≡ p_offset mod p_align; non-overlap is \
      de facto from linker)"

end LeanLoad.Parse.File

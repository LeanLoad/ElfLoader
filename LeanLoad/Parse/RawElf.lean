/-
Aggregate ELF byte parser: walks an entire ELF the way a loader needs
to — header → program headers → `.dynamic` → string table → dynamic
symbol table → relocation tables → `DT_NEEDED` strings → init/fini
lists.

This file is *only* the byte-decode stage. It returns a `RawElf`
with no semantic checks: malformed PT_LOAD shape, unhost-able
relocations, and unsupported ELF class/endianness are all caught
later by `Elaborate.elaborate`.

The dynamic symbol-table count comes from `DT_HASH`'s `nchain` field
(gabi 08 § Hash Table). Modern toolchains default to `--hash-style=
gnu`, which would emit only `DT_GNU_HASH` and require chain walking;
the build (`Makefile`) requests `--hash-style=both` so `DT_HASH` is
always available, letting this parser stay simple.

Raw types live in `Parse.Structs`. Variable-length parser and
by-tag lookups for the `.dynamic` array live in `Parse.Dynamic`.
-/

import LeanLoad.Parse.Decode
import LeanLoad.Parse.Structs
import LeanLoad.Parse.Dynamic
import LeanLoad.Runtime

namespace LeanLoad.Parse

-- ============================================================================
-- Virtual-address ↔ file-offset translation. Used during parse to
-- read sections whose offsets in the file we know only via
-- (link-time) virtual addresses stored in `.dynamic`.
-- ============================================================================

/-- Per-phdr offset translation: `some off` if `ph` is a PT_LOAD
    that covers `va`, `none` otherwise. -/
private def offsetIn (va : UInt64) (ph : RawPhdr) : Option Nat :=
  if ph.p_type == PT_LOAD ∧ ph.p_vaddr ≤ va ∧ va < ph.p_vaddr + ph.p_memsz then
    some ((va - ph.p_vaddr).toNat + ph.p_offset.toNat)
  else none

/-- Translate a virtual address to a file offset by walking the
    `PT_LOAD` segments. Returns `none` if no `PT_LOAD` covers `va`. -/
def vaToOffset (phdrs : Array RawPhdr) (va : UInt64) : Option Nat :=
  phdrs.findSome? (offsetIn va)

/-- Correctness witness: a successful `vaToOffset` returns an offset
    derived from a covering PT_LOAD phdr in `phdrs`. -/
theorem vaToOffset_eq_some
    {phdrs : Array RawPhdr} {va : UInt64} {off : Nat}
    (h : vaToOffset phdrs va = some off) :
    ∃ ph ∈ phdrs, ph.p_type = PT_LOAD ∧
                  ph.p_vaddr ≤ va ∧ va < ph.p_vaddr + ph.p_memsz ∧
                  off = (va - ph.p_vaddr).toNat + ph.p_offset.toNat := by
  unfold vaToOffset at h
  obtain ⟨ph, h_mem, h_some⟩ := Array.exists_of_findSome?_eq_some h
  unfold offsetIn at h_some
  split at h_some
  · rename_i hcond
    obtain ⟨h_load, h_lo, h_hi⟩ := hcond
    refine ⟨ph, h_mem, beq_iff_eq.mp h_load, h_lo, h_hi, ?_⟩
    exact (Option.some_inj.mp h_some).symm
  · contradiction

section Example
private def phdrs : Array RawPhdr := #[
  { (default : RawPhdr) with
    p_type := PT_LOAD,
    p_vaddr := 0x1000, p_memsz := 0x1000,
    p_offset := 0x1000, p_filesz := 0x1000 },
  { (default : RawPhdr) with
    p_type := PT_LOAD,
    p_vaddr := 0x3000, p_memsz := 0x500,
    p_offset := 0x2000, p_filesz := 0x500 } ]

#guard vaToOffset phdrs 0x1000 = some 0x1000
#guard vaToOffset phdrs 0x1abc = some 0x1abc
#guard vaToOffset phdrs 0x3010 = some 0x2010
#guard vaToOffset phdrs 0x0fff = none
#guard vaToOffset phdrs 0x2500 = none
#guard vaToOffset phdrs 0x3500 = none
end Example

-- ============================================================================
-- RawElf — output of `parse`. Bytes decoded only; no witnesses.
-- ============================================================================

/-- The raw byte-decode of an ELF file. Output of `parse`, input to
    `Elaborate.elaborate`. -/
structure RawElf where
  header  : RawEhdr
  phdrs   : Array RawPhdr
  /-- The `.dynamic` array, empty if no `PT_DYNAMIC`. -/
  dyn     : Array RawDyn
  /-- The dynamic string table (`DT_STRTAB`), empty if absent. -/
  strtab  : RawStrtab
  /-- Dynamic symbol table (`DT_SYMTAB`). Empty if no hash entry
      tells us the count. -/
  symtab  : Array RawSym
  /-- `DT_NEEDED` offsets into `strtab`, in dynamic-array order. -/
  needed  : Array UInt64
  /-- `DT_SONAME` offset into `strtab`, if present. -/
  soname  : Option UInt64
  /-- `DT_RUNPATH` offset into `strtab`, falling back to `DT_RPATH`. -/
  runpath : Option UInt64
  /-- General `Rela` relocations from `DT_RELA`, ungrouped. -/
  rela    : Array RawRela
  /-- PLT relocations from `DT_JMPREL`, ungrouped. -/
  jmprel  : Array RawRela
  /-- `DT_INIT_ARRAY` entries — already parsed from the file bytes. -/
  initArr : Array UInt64
  deriving Inhabited

end LeanLoad.Parse

-- ============================================================================
-- Helpers and the `parse` entry point.
-- ============================================================================

namespace LeanLoad.Parse.RawElf

open LeanLoad
open LeanLoad.Parse

/-- `pread` `len` bytes at `offset` and run `parser` from the start. -/
private def parseSection {α} (h : Runtime.FileHandle)
    (label : String) (offset : UInt64) (len : UInt64) (parser : Parser α) : IO α := do
  let bytes ← Runtime.pread h offset len
  match Parser.run bytes parser with
  | .ok v    => pure v
  | .error e => throw (IO.userError s!"parse {label}: {e}")

/-- Resolve `vaddr` to a file offset; throw if no `PT_LOAD` covers it. -/
private def vaToOffsetIO (phdrs : Array RawPhdr) (label : String)
    (vaddr : UInt64) : IO Nat :=
  match vaToOffset phdrs vaddr with
  | some off => pure off
  | none     => throw (IO.userError s!"parse {label}: va 0x{vaddr.toNat} not in any PT_LOAD")

-- ============================================================================
-- Per-section parsers. Each reads one well-defined slice of the file;
-- `parse` (below) chains them. Every helper takes the inputs it
-- actually needs (no shared state), so each is testable in isolation.
-- ============================================================================

private def parseEhdr (h : Runtime.FileHandle) : IO RawEhdr :=
  parseSection h "ehdr" 0 64 (BytesDecode.decode : Parser RawEhdr)

private def parsePhdrs (h : Runtime.FileHandle)
    (header : RawEhdr) : IO (Array RawPhdr) :=
  let nbytes := (header.e_phnum.toNat * RawPhdrSize).toUInt64
  parseSection h "phdrs" header.e_phoff nbytes
    (decodeArray (α := RawPhdr) 0 header.e_phnum.toNat)

private def parseDynamic (h : Runtime.FileHandle)
    (phdrs : Array RawPhdr) : IO (Array RawDyn) :=
  match phdrs.find? (·.p_type == PT_DYNAMIC) with
  | none    => pure #[]
  | some ph =>
    parseSection h "dynamic" ph.p_offset ph.p_filesz
      (Parse.Dynamic.parseTable 0 ph.p_filesz.toNat)

private def parseStrtab (h : Runtime.FileHandle)
    (phdrs : Array RawPhdr) (dyn : Array RawDyn) : IO RawStrtab :=
  match Parse.Dynamic.pair? dyn DT_STRTAB DT_STRSZ with
  | none             => pure (ByteArray.mk #[])
  | some (vaddr, sz) => do
    let off ← vaToOffsetIO phdrs "DT_STRTAB" vaddr
    Runtime.pread h off.toUInt64 sz

/-- Read `nchain` from `DT_HASH` to derive the dynsym count. The
    build's `--hash-style=both` guarantees `DT_HASH` is present;
    GNU-only outputs would require chain walking we don't model. -/
private def parseSymCount (h : Runtime.FileHandle)
    (phdrs : Array RawPhdr) (dyn : Array RawDyn) : IO Nat :=
  match Parse.Dynamic.val? dyn DT_HASH with
  | none => pure 0
  | some hashVa => do
    let off ← vaToOffsetIO phdrs "DT_HASH" hashVa
    parseSection h "DT_HASH" off.toUInt64 8
      (do let _ ← u32le; let nchain ← u32le; return nchain.toNat)

private def parseSymtab (h : Runtime.FileHandle)
    (phdrs : Array RawPhdr) (dyn : Array RawDyn) (symCount : Nat) : IO (Array RawSym) :=
  if symCount == 0 then pure #[]
  else match Parse.Dynamic.val? dyn DT_SYMTAB with
    | none       => pure #[]
    | some vaddr => do
      let off ← vaToOffsetIO phdrs "DT_SYMTAB" vaddr
      parseSection h "DT_SYMTAB" off.toUInt64 (symCount * RawSymSize).toUInt64
        (decodeArray (α := RawSym) 0 symCount)

/-- Read a fixed-size sized table from a `(addrTag, sizeTag)` pair in
    `.dynamic`: `addrTag` gives the table's vaddr, `sizeTag` its byte
    size. Returns `#[]` if either tag is absent. -/
private def parseSizedTable {α} [BytesDecode α] (entrySize : Nat)
    (h : Runtime.FileHandle)
    (phdrs : Array RawPhdr) (dyn : Array RawDyn)
    (addrTag sizeTag : UInt64) (label : String) : IO (Array α) := do
  match Parse.Dynamic.pair? dyn addrTag sizeTag with
  | none             => pure #[]
  | some (vaddr, sz) =>
    let off ← vaToOffsetIO phdrs label vaddr
    parseSection h label off.toUInt64 sz
      (decodeArray (α := α) 0 (sz.toNat / entrySize))

-- ============================================================================
-- Top-level entry. Reads as a checklist of "what an ELF has, in
-- order"; each line is either a typed section parse or a tagged
-- lookup into `.dynamic`.
-- ============================================================================

/-- Parse an ELF file via per-section `pread`s on a `FileHandle`.
    Each section's bytes live in their own small `ByteArray` and are
    GC'd after parsing — no whole-file `ByteArray` is constructed. -/
def parse (h : Runtime.FileHandle) : IO RawElf := do
  let header   ← parseEhdr h
  let phdrs    ← parsePhdrs h header
  let dyn      ← parseDynamic h phdrs
  let strtab   ← parseStrtab h phdrs dyn
  let symCount ← parseSymCount h phdrs dyn
  let symtab   ← parseSymtab h phdrs dyn symCount

  let needed   := (Parse.Dynamic.findAll dyn DT_NEEDED).map (·.d_un)
  let soname   := Parse.Dynamic.val? dyn DT_SONAME
  let runpath  := Parse.Dynamic.val? dyn DT_RUNPATH <|> Parse.Dynamic.val? dyn DT_RPATH

  let rela     ← parseSizedTable RawRelaSize h phdrs dyn DT_RELA       DT_RELASZ       "DT_RELA"
  let jmprel   ← parseSizedTable RawRelaSize h phdrs dyn DT_JMPREL     DT_PLTRELSZ     "DT_JMPREL"
  let initArr  ← parseSizedTable 8           h phdrs dyn DT_INIT_ARRAY DT_INIT_ARRAYSZ "DT_INIT_ARRAY"

  return {
    header, phdrs, dyn, strtab, symtab, needed, soname, runpath,
    rela, jmprel, initArr
  }

end LeanLoad.Parse.RawElf

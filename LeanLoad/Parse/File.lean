/-
Aggregate ELF byte parser: walks an entire ELF the way a loader needs
to — header → program headers → `.dynamic` → string table → dynamic
symbol table → relocation tables → `DT_NEEDED` strings → init/fini
lists.

This file is *only* the byte-decode stage. It returns a `RawElf`
with no semantic checks: malformed PT_LOAD shape, unhost-able
relocations, and unsupported ELF class/endianness are all caught
later by `Elaborate.elaborate`.

The dynamic symbol-table count is taken from `DT_HASH`'s `nchain`
field (gabi 08 § Hash Table) when present, falling back to walking
`DT_GNU_HASH`'s chain table when only the GNU extension is emitted
(gnu-gabi `program-loading-and-dynamic-linking.txt` § Hashes). Modern
Linux toolchains default to gnu-only.

Raw types live in `Parse.Raw`. Variable-length parsers (`.dynamic`,
GNU hash) live in `Parse.Dynamic` and `Parse.GnuHash`.
-/

import LeanLoad.Parse.Bytes
import LeanLoad.Parse.Structs
import LeanLoad.Parse.Dynamic
import LeanLoad.Parse.GnuHash
import LeanLoad.Runtime

namespace LeanLoad.Parse

open LeanLoad.Parse.Bytes

-- ============================================================================
-- Virtual-address ↔ file-offset translation (used during parse to
-- read sections whose offsets are given as virtual addresses).
-- ============================================================================

/-- Witness packaged with `vaToOffset`'s `some` branch. -/
abbrev VaToOffsetSpec (phdrs : Array RawPhdr) (va : UInt64) (off : Nat) : Prop :=
  ∃ ph ∈ phdrs,
    ph.p_type = PT_LOAD ∧
    ph.p_vaddr ≤ va ∧
    va < ph.p_vaddr + ph.p_memsz ∧
    off = (va - ph.p_vaddr).toNat + ph.p_offset.toNat

/-- Translate a virtual address to a file offset by walking the
    `PT_LOAD` segments. Returns `none` if no `PT_LOAD` covers it. -/
def vaToOffset (phdrs : Array RawPhdr) (va : UInt64) :
    Option { off : Nat // VaToOffsetSpec phdrs va off } := Id.run do
  for h : i in [:phdrs.size] do
    let ph := phdrs[i]
    if h_load : ph.p_type = PT_LOAD then
      if h_lo : ph.p_vaddr ≤ va then
        if h_hi : va < ph.p_vaddr + ph.p_memsz then
          let off := (va - ph.p_vaddr).toNat + ph.p_offset.toNat
          have h_mem : ph ∈ phdrs := phdrs.getElem_mem h.upper
          return some ⟨off, ⟨ph, h_mem, h_load, h_lo, h_hi, rfl⟩⟩
  return none

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

private def vaToOffsetNat (phdrs : Array RawPhdr) (va : UInt64) : Option Nat :=
  (vaToOffset phdrs va).map (·.val)

#guard vaToOffsetNat phdrs 0x1000 = some 0x1000
#guard vaToOffsetNat phdrs 0x1abc = some 0x1abc
#guard vaToOffsetNat phdrs 0x3010 = some 0x2010
#guard vaToOffsetNat phdrs 0x0fff = none
#guard vaToOffsetNat phdrs 0x2500 = none
#guard vaToOffsetNat phdrs 0x3500 = none
end Example

-- ============================================================================
-- RawElf — output of `parse`. Bytes decoded only; no witnesses.
-- ============================================================================

/-- The raw byte-decode of an ELF file: structurally parsed but with
    no validation witnesses and no relocations grouped by segment.
    Output of `parse`, input to `Elaborate.elaborate`. -/
structure RawElf where
  header  : RawEhdr
  phdrs   : Array RawPhdr
  /-- The `.dynamic` array, empty if no `PT_DYNAMIC`. -/
  dyn     : Array RawDyn
  /-- The dynamic string table (`DT_STRTAB`), empty if absent. -/
  strtab  : RawStrtab
  /-- Dynamic symbol table (`DT_SYMTAB`), sized via `DT_HASH`'s
      `nchain`. Empty if neither is present. -/
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

namespace LeanLoad.Parse.File

open LeanLoad
open LeanLoad.Parse
open LeanLoad.Parse.Bytes

private def dynVal? (dyn : Array RawDyn) (tag : UInt64) : Option UInt64 :=
  (Parse.Dynamic.find? dyn tag).map (·.d_un)

private def dynPair? (dyn : Array RawDyn) (tagA tagB : UInt64) : Option (UInt64 × UInt64) := do
  let a ← dynVal? dyn tagA
  let b ← dynVal? dyn tagB
  return (a, b)

/-- Find the `PT_LOAD` whose file range covers `off`. Used to upper-
    bound `DT_GNU_HASH`'s chain (no size field in the dynamic table). -/
private def containingPTLoad (phdrs : Array RawPhdr) (off : Nat) : Option RawPhdr :=
  phdrs.find? fun ph =>
    ph.p_type == PT_LOAD &&
    ph.p_offset.toNat ≤ off &&
    off < ph.p_offset.toNat + ph.p_filesz.toNat

/-- `pread` `len` bytes at `offset` (via the runtime capability) and
    run `parser` from the start. -/
private def parseSection {α} (rt : Runtime.Ops) (h : Runtime.FileHandle)
    (label : String) (offset : UInt64) (len : USize) (parser : Parser α) : IO α := do
  let bytes ← rt.pread h offset len
  match Parser.run bytes parser with
  | .ok v    => pure v
  | .error e => throw (IO.userError s!"parse {label}: {e}")

/-- Resolve `vaddr` to a file offset; throw if no `PT_LOAD` covers it. -/
private def vaToOffsetIO (phdrs : Array RawPhdr) (label : String)
    (vaddr : UInt64) : IO Nat :=
  match vaToOffset phdrs vaddr with
  | some ⟨off, _⟩ => pure off
  | none          => throw (IO.userError s!"parse {label}: va 0x{vaddr.toNat} not in any PT_LOAD")

/-- Parse an ELF file via per-section `pread`s on a `FileHandle`.
    Each section's bytes live in their own small `ByteArray` and are
    GC'd after parsing — no whole-file `ByteArray` is constructed.

    Returns `RawElf` — bytes-decoded only. Validation, relocation
    grouping, and the gabi-07 well-formedness check happen
    downstream in `Elaborate.elaborate`. -/
def parse (rt : Runtime.Ops) (h : Runtime.FileHandle) : IO RawElf := do
  let header ← parseSection rt h "header" 0 64 (BytesDecode.decode : Parser RawEhdr)

  let phdrTableSize := (header.e_phnum.toNat * RawPhdrSize).toUSize
  let phdrs ← parseSection rt h "phdrs" header.e_phoff phdrTableSize
                (Bytes.decodeArray (α := RawPhdr) 0 header.e_phnum.toNat)

  let dyn ← match phdrs.find? (·.p_type == PT_DYNAMIC) with
    | none    => pure #[]
    | some ph =>
      parseSection rt h "dynamic" ph.p_offset ph.p_filesz.toNat.toUSize
        (Parse.Dynamic.parseTable 0 ph.p_filesz.toNat)

  let strtab : RawStrtab ← match dynPair? dyn DT_STRTAB DT_STRSZ with
    | none             => pure (ByteArray.mk #[])
    | some (vaddr, sz) =>
      let off ← vaToOffsetIO phdrs "DT_STRTAB" vaddr
      rt.pread h off.toUInt64 sz.toNat.toUSize

  let symCount : Nat ←
    match dynVal? dyn DT_HASH, dynVal? dyn DT_GNU_HASH with
    | some hashVa, _ =>
      let off ← vaToOffsetIO phdrs "DT_HASH" hashVa
      parseSection rt h "DT_HASH" off.toUInt64 8
        (do let _ ← Bytes.u32le; let nchain ← Bytes.u32le; return nchain.toNat)
    | none, some gnuHashVa =>
      let off ← vaToOffsetIO phdrs "DT_GNU_HASH" gnuHashVa
      match containingPTLoad phdrs off with
      | none    => throw (IO.userError s!"parse DT_GNU_HASH: offset 0x{off} in no PT_LOAD")
      | some ph =>
        let segEnd  := ph.p_offset.toNat + ph.p_filesz.toNat
        let availLen := (segEnd - off).toUSize
        parseSection rt h "DT_GNU_HASH" off.toUInt64 availLen
          (Parse.GnuHash.parseSymCount 0)
    | none, none => pure 0

  let symtab ← if symCount == 0 then pure #[]
    else match dynVal? dyn DT_SYMTAB with
      | none       => pure #[]
      | some vaddr =>
        let off := ← vaToOffsetIO phdrs "DT_SYMTAB" vaddr
        let symSize := (symCount * RawSymSize).toUSize
        parseSection rt h "DT_SYMTAB" off.toUInt64 symSize
          (Bytes.decodeArray (α := RawSym) 0 symCount)

  let needed  := (Parse.Dynamic.findAll dyn DT_NEEDED).map (·.d_un)
  let soname  := dynVal? dyn DT_SONAME
  let runpath := dynVal? dyn DT_RUNPATH <|> dynVal? dyn DT_RPATH

  let parseRelaPair (tagAddr tagSz : UInt64) (label : String) : IO (Array RawRela) := do
    match dynPair? dyn tagAddr tagSz with
    | none             => pure #[]
    | some (vaddr, sz) =>
      let off ← vaToOffsetIO phdrs label vaddr
      let count := sz.toNat / RawRelaSize
      parseSection rt h label off.toUInt64 sz.toNat.toUSize
        (Bytes.decodeArray (α := RawRela) 0 count)
  let rela   ← parseRelaPair DT_RELA   DT_RELASZ   "DT_RELA"
  let jmprel ← parseRelaPair DT_JMPREL DT_PLTRELSZ "DT_JMPREL"

  let initArr ← match dynPair? dyn DT_INIT_ARRAY DT_INIT_ARRAYSZ with
    | none             => pure #[]
    | some (vaddr, sz) =>
      let off ← vaToOffsetIO phdrs "DT_INIT_ARRAY" vaddr
      let count := sz.toNat / 8
      parseSection rt h "DT_INIT_ARRAY" off.toUInt64 sz.toNat.toUSize
        (Bytes.decodeArray (α := UInt64) 0 count)

  return {
    header, phdrs, dyn, strtab, symtab, needed, soname, runpath,
    rela, jmprel, initArr
  }

end LeanLoad.Parse.File

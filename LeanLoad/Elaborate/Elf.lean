/-
ELF elaboration — pure stage between byte decoding (`Parse`) and the
planner.

Takes a `Parse.RawElf` (bytes-decoded only, no semantic checks) and
returns an `Elaborate.Elf`:

  - 64-bit / little-endian sanity checks on the header (`ELFCLASS64`,
    `ELFDATA2LSB`).
  - Every `DT_RELA` / `DT_JMPREL` entry located against a covering
    PT_LOAD segment, witnessed by the subtype on
    `Elaborate.Segment.{rela, jmprel}`.
  - Per-segment relocation grouping built into `Array Elaborate.Segment`.
  - PT_LOAD well-formedness witness (`segmentsWf : WellFormed segments`)
    carried for downstream consumers.
  - Symbol names pre-resolved against the dynamic string table.

Constants and per-section semantics live in:
  - `Header.lean` — `ELFCLASS*`, `ELFDATA*`, `ET_*`
  - `Strtab.lean` — `RawStrtab.lookup`
  - `Symbol.lean` — `STB/STT/SHN_*`, `RawSym` predicates, `Symbol`
  - `Reloc.lean` — `RawRela.sym/type` + relocation formulas
  - `Segment.lean` — single-segment containment + bundle
  - `WellFormed.lean` — gabi-07 array invariants

Failures are `Except String`: malformed ELF class/endianness,
malformed PT_LOAD shape, or any rela whose write window doesn't fit
a PT_LOAD.
-/

import LeanLoad.Parse.RawElf
import LeanLoad.Elaborate.Header
import LeanLoad.Elaborate.Strtab
import LeanLoad.Elaborate.Symbol
import LeanLoad.Elaborate.Segment
import LeanLoad.Elaborate.WellFormed

namespace LeanLoad.Elaborate

open LeanLoad
open LeanLoad.Parse (RawElf RawPhdr RawRela RawSym)

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
  /-- gabi-07 well-formedness witness, established by `elaborate`.
      Downstream consumers read `segmentsWf.sorted`,
      `segmentsWf.alignCong`, … via field projections without
      re-checking. -/
  segmentsWf : WellFormed segments

instance : Inhabited Elf where
  default :=
    { header := default, symtab := #[], needed := #[],
      soname := none, runpath := none, initArr := #[],
      segments := #[], segmentsWf := WellFormed_nil }

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

/-- Elaborate a `RawElf`: check ELF class/endian, locate every rela
    against a PT_LOAD segment, bundle into `Array Segment`, verify
    gabi-07 well-formedness, pre-resolve every symbol's name. -/
def elaborate (raw : RawElf) : Except String Elf := do
  if raw.header.ident.ei_class != ELFCLASS64 then
    .error s!"elaborate: only ELFCLASS64 supported \
      (got ei_class={raw.header.ident.ei_class})"
  if raw.header.ident.ei_data != ELFDATA2LSB then
    .error s!"elaborate: only little-endian supported \
      (got ei_data={raw.header.ident.ei_data})"
  let loadable := fromPhdrs raw.phdrs
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
    { sym, name := raw.strtab.lookup sym.st_name.toNat }
  let needed  := raw.needed.filterMap (raw.strtab.lookup ·.toNat)
  let soname  := raw.soname.bind (raw.strtab.lookup ·.toNat)
  let runpath := raw.runpath.bind (raw.strtab.lookup ·.toNat)
  if h : WellFormed segments then
    return {
      header := raw.header, symtab,
      needed, soname, runpath,
      initArr := raw.initArr, segments,
      segmentsWf := h }
  else
    .error "elaborate: malformed PT_LOAD segments \
      (gabi-07 mandates: sort by p_vaddr, p_filesz ≤ p_memsz, p_align \
      is a power of 2, p_vaddr ≡ p_offset mod p_align; non-overlap is \
      de facto from linker)"

end LeanLoad.Elaborate

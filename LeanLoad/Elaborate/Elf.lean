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
    carried for downstream consumers — defined in this file.
  - Symbol names pre-resolved against the dynamic string table.

Constants and per-section semantics live in:
  - `Header.lean` — `ELFCLASS*`, `ELFDATA*`, `ET_*`
  - `Strtab.lean` — `RawStrtab.lookup`
  - `Symbol.lean` — `STB/STT/SHN_*`, `RawSym` predicates, `Symbol`
  - `Reloc.lean` — `RawRela.sym/type` + relocation formulas
  - `Segment.lean` — single-segment containment + bundle

Failures are `Except String`: malformed ELF class/endianness,
malformed PT_LOAD shape, or any rela whose write window doesn't fit
a PT_LOAD.
-/

import LeanLoad.Parse.RawElf
import LeanLoad.Elaborate.Header
import LeanLoad.Elaborate.Strtab
import LeanLoad.Elaborate.Symbol
import LeanLoad.Elaborate.Segment

namespace LeanLoad.Elaborate

open LeanLoad
open LeanLoad.Parse (RawElf RawPhdr RawRela RawSym)

-- ============================================================================
-- PT_LOAD-array well-formedness — the per-pair gabi-07 invariants on
-- `Array Segment`. Per-segment invariants are validated by
-- `Segment.ofPhdr` and discarded (no proof field stored on `Segment`).
--
-- Spec: gabi 07 § Program Loading. These are *spec-level* (gabi
-- vaddr/memsz ordering); page-aligned non-overlap is a separate
-- runtime check via `Plan.segmentsSorted` (over `SegmentPlan`s).
--
-- The two predicates live as standalone defs (not bundled in a
-- `WellFormed` wrapper) so `Elf` can carry them as direct fields.
-- Bound the index in front of the quantifier so each Prop is decidable
-- via `Nat.decidableBAllLT`.
-- ============================================================================

/-- gabi 07 § Program Loading: PT_LOAD entries appear in `p_vaddr` order. -/
def Sorted (segs : Array Segment) : Prop :=
  ∀ i, ∀ _ : i < segs.size, ∀ j, ∀ _ : j < segs.size,
    i < j → segs[i].vaddr ≤ segs[j].vaddr

/-- *De facto*, not gabi-mandated: PT_LOAD `[p_vaddr, p_vaddr +
    p_memsz)` ranges are pairwise disjoint. -/
def NonOverlap (segs : Array Segment) : Prop :=
  ∀ i, ∀ _ : i < segs.size, ∀ j, ∀ _ : j < segs.size,
    i < j → segs[i].vaddr + segs[i].memsz ≤ segs[j].vaddr

instance (segs : Array Segment) : Decidable (Sorted segs) := by
  unfold Sorted; infer_instance
instance (segs : Array Segment) : Decidable (NonOverlap segs) := by
  unfold NonOverlap; infer_instance

-- ============================================================================
-- Phdr coverage — a PT_LOAD segment maps the program-header table to
-- the loaded image at virtual address `phoff`. Requires `vaddr =
-- offset` for the covering segment so `mainBase + phoff` equals the
-- runtime `AT_PHDR` without an offset→vaddr translation. By gabi-07
-- convention the first PT_LOAD has both at 0 (or the same aligned
-- base) and contains the ELF header + phdr table.
-- ============================================================================

/-- The PT_LOAD segment `s` covers the program-header table at file
    offset `phoff` of byte length `nbytes`, AND its `vaddr` equals its
    `offset` (so `runtime_addr = mainBase + phoff` is consistent with
    the kernel's `AT_PHDR`). -/
def coversPhdrs (s : Segment) (phoff : UInt64) (nbytes : Nat) : Prop :=
  s.vaddr = s.offset ∧
  s.vaddr.toNat ≤ phoff.toNat ∧
  phoff.toNat + nbytes ≤ s.vaddr.toNat + s.memsz.toNat

instance (s : Segment) (phoff : UInt64) (nbytes : Nat) :
    Decidable (coversPhdrs s phoff nbytes) := by
  unfold coversPhdrs; infer_instance

/-- Some PT_LOAD segment covers the phdr table (per `coversPhdrs`).
    Bounded `∃` so it's decidable via `Nat.decidableBExLT`. -/
def PhdrCovered (segs : Array Segment) (phoff : UInt64) (nbytes : Nat) : Prop :=
  ∃ i, ∃ _ : i < segs.size, coversPhdrs segs[i] phoff nbytes

instance (segs : Array Segment) (phoff : UInt64) (nbytes : Nat) :
    Decidable (PhdrCovered segs phoff nbytes) := by
  unfold PhdrCovered; infer_instance

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
  /-- Typed `e_type` (gabi 02). Planner code matches on this. -/
  elfType  : ElfType
  /-- Typed `e_machine` — drives per-arch relocation formula
      selection (`formulaFor`). Closed enum: only architectures
      LeanLoad supports. -/
  machine  : Machine
  /-- `e_entry` — process entry point virtual address. -/
  entry    : UInt64
  /-- `e_phoff` — program-header table file offset (used by Exec to
      synthesize `AT_PHDR` for the kernel auxv). -/
  phoff    : UInt64
  /-- `e_phnum` — number of program-header entries. -/
  phnum    : UInt16
  symtab   : Array Symbol
  needed   : Array String
  soname   : Option String
  runpath  : Option String
  initArr  : Array UInt64
  /-- One bundle per PT_LOAD, in phdr order, with relas grouped by
      the segment they target. -/
  segments : Array Segment
  /-- gabi 07: PT_LOAD entries are in `p_vaddr` order. -/
  segmentsSorted     : Sorted segments
  /-- De-facto: PT_LOAD ranges are pairwise disjoint. -/
  segmentsNonOverlap : NonOverlap segments
  /-- The program-header table is mapped to the loaded image at
      virtual address `phoff` — i.e. some PT_LOAD with `vaddr = offset`
      covers `[phoff, phoff + phnum × RawPhdrSize)`. Lets `Main.realize`
      pass `mainBase + phoff` as `AT_PHDR` to `execAndJump` without
      offset-to-vaddr translation — and proves that the runtime trust
      assumption is met at elaborate time. -/
  phdrCovered : PhdrCovered segments phoff (Parse.RawPhdrSize * phnum.toNat)

-- ============================================================================
-- elaborate: RawElf → Except String Elf
-- ============================================================================

/-- Find the PT_LOAD index that fully covers `r`'s 8-byte write
    window, with its containment witness. Returns `none` if no
    segment covers the write range. -/
private def locateRela (segs : Array RawPhdr) (r : RawRela) :
    Option (Σ' (i : Fin segs.size),
              coversRela segs[i].p_vaddr segs[i].p_memsz r.r_offset) := Id.run do
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
  let loadable := raw.phdrs.filter (·.p_type == Parse.PT_LOAD)
  -- Per-rela "tagged with its segment index" (Sigma — destructurable).
  let GEntry := Σ i : Fin loadable.size,
                  { r : RawRela //
                    coversRela loadable[i].p_vaddr loadable[i].p_memsz r.r_offset }
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
      Array { r : RawRela //
        coversRela loadable[bucketIdx].p_vaddr loadable[bucketIdx].p_memsz r.r_offset } :=
    bucket.filterMap fun ⟨i, ⟨r, h_in⟩⟩ =>
      if h_eq : i = bucketIdx then some ⟨r, h_eq ▸ h_in⟩
      else none
  -- Each loadable phdr is PT_LOAD by construction (filtered above);
  -- `Segment.ofPhdr` decidably checks each per-segment gabi-07
  -- invariant and the 48-bit address bound, failing with a typed error.
  let mut segmentsAcc : Array Segment := #[]
  for h : i in [:loadable.size] do
    let bucketIdx : Fin loadable.size := ⟨i, h.upper⟩
    let phdr := loadable[bucketIdx]
    let rB := relaBuckets[i]?.getD #[]
    let jB := jmprelBuckets[i]?.getD #[]
    match Segment.ofPhdr phdr (buildBucket bucketIdx rB) (buildBucket bucketIdx jB) with
    | .ok seg  => segmentsAcc := segmentsAcc.push seg
    | .error e => .error s!"elaborate: segment[{i}]: {e}"
  let segments := segmentsAcc
  let some elfType := ElfType.ofRaw raw.header.e_type
    | .error s!"elaborate: unknown e_type={raw.header.e_type}"
  if elfType == .exec then
    .error s!"elaborate: ET_EXEC not supported — LeanLoad expects PIE \
      (ET_DYN) inputs only. Recompile with -fPIE -pie."
  let some machine := Machine.ofRaw raw.header.e_machine
    | .error s!"elaborate: unsupported e_machine={raw.header.e_machine} \
        (need 62=EM_X86_64 or 183=EM_AARCH64)"
  let symtab : Array Symbol ← raw.symtab.mapM (Symbol.ofRaw raw.strtab)
  let needed  := raw.needed.filterMap (raw.strtab.lookup ·.toNat)
  let soname  := raw.soname.bind (raw.strtab.lookup ·.toNat)
  let runpath := raw.runpath.bind (raw.strtab.lookup ·.toNat)
  if h_wf : Sorted segments ∧ NonOverlap segments then
    let phdr_nbytes : Nat := Parse.RawPhdrSize * raw.header.e_phnum.toNat
    if h_phdr : PhdrCovered segments raw.header.e_phoff phdr_nbytes then
      return {
        elfType, machine,
        entry := raw.header.e_entry,
        phoff := raw.header.e_phoff,
        phnum := raw.header.e_phnum,
        symtab,
        needed, soname, runpath,
        initArr := raw.initArr, segments,
        segmentsSorted := h_wf.left, segmentsNonOverlap := h_wf.right,
        phdrCovered := h_phdr }
    else
      .error s!"elaborate: phdr table at file offset \
        0x{raw.header.e_phoff.toNat} (size {phdr_nbytes}) is not covered \
        by any PT_LOAD with vaddr=offset; AT_PHDR cannot be computed as \
        mainBase + phoff"
  else
    .error "elaborate: PT_LOAD segments not sorted or overlap \
      (gabi-07 § Program Loading: sort by p_vaddr; non-overlap is \
      de facto from linker)"

end LeanLoad.Elaborate

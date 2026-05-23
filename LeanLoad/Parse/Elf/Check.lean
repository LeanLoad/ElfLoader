/-
Checked ELF construction.
-/

import LeanLoad.Parse.Dynamic.Types
import LeanLoad.Parse.Elf.Checked

namespace LeanLoad.Parse

namespace Elf

namespace RelocBuckets

/-- A relocation paired with the checked segment index whose memory range
    contains its 8-byte write window. -/
abbrev Entry (segments : SegmentTable) :=
  Σ i : Fin segments.items.size,
    Rela segments.items[i].phdr.p_vaddr segments.items[i].phdr.p_memsz

/-- Find the PT_LOAD index that fully covers `r`'s 8-byte write window. -/
private def locate (segments : SegmentTable) (r : RawRela) :
    Option (Entry segments) := Id.run do
  for h : i in [:segments.items.size] do
    let idx : Fin segments.items.size := ⟨i, h.upper⟩
    let s := segments.items[idx]
    if h_lo : s.phdr.p_vaddr.toNat ≤ r.r_offset.toNat then
      if h_hi : r.r_offset.toNat + 8 ≤ s.phdr.p_vaddr.toNat + s.phdr.p_memsz.toNat then
        return some ⟨idx, { raw := r, covered := ⟨h_lo, h_hi⟩ }⟩
  return none

/-- Bucket a flat relocation table by containing checked PT_LOAD segment. -/
private def groupOne (label : String) (segments : SegmentTable) (rs : Array RawRela) :
    Except String (Array (Array (Entry segments))) := do
  let mut buckets : Array (Array (Entry segments)) := Array.replicate segments.items.size #[]
  for r in rs do
    match locate segments r with
    | none =>
        .error s!"parse {label}: rela r_offset=0x{r.r_offset.toNat} \
          not covered by any PT_LOAD segment"
    | some ⟨i, h_in⟩ =>
        let entry : Entry segments := ⟨i, h_in⟩
        buckets := buckets.modify i.val (·.push entry)
  return buckets

/-- Recover the dependent relocation array for one bucket. -/
private def buildBucket (segments : SegmentTable) (bucketIdx : Fin segments.items.size)
    (bucket : Array (Entry segments)) :
    Array (Rela segments.items[bucketIdx].phdr.p_vaddr
      segments.items[bucketIdx].phdr.p_memsz) :=
  bucket.filterMap fun ⟨i, rela⟩ =>
    if h_eq : i = bucketIdx then
      some { raw := rela.raw, covered := h_eq ▸ rela.covered }
    else none

/-- Attach flat `DT_RELA` and `DT_JMPREL` tables to their checked PT_LOAD
    segments, preserving each segment's existing layout witnesses. -/
private def attach (segments : SegmentTable) (rela jmprel : Array RawRela) :
    Except String ((i : Fin segments.items.size) → Relocs segments.items[i]) := do
  let relaBuckets   ← groupOne "DT_RELA" segments rela
  let jmprelBuckets ← groupOne "DT_JMPREL" segments jmprel
  return fun bucketIdx =>
    let rB := relaBuckets[bucketIdx.val]?.getD #[]
    let jB := jmprelBuckets[bucketIdx.val]?.getD #[]
    { rela := buildBucket segments bucketIdx rB
      jmprel := buildBucket segments bucketIdx jB }

end RelocBuckets

/-- Check a dynamic staging image into the final witness-carrying `Elf`. Header
    policy, PT_LOAD well-formedness, and dynamic string resolution are already
    carried by `Dynamic`. -/
def ofDynamic (raw : Dynamic) : Except String Elf := do
  let header := raw.header
  let relocs ← RelocBuckets.attach raw.segments raw.rela raw.jmprel
  let symtab : Array Symbol ← raw.symtab.mapM (Symbol.ofRaw raw.strtab)
  let initArr ← checkInitFiniArray "DT_INIT_ARRAY" raw.segments raw.initArr
  let finiArr ← checkInitFiniArray "DT_FINI_ARRAY" raw.segments raw.finiArr
  return {
    header,
    symtab,
    needed := raw.needed,
    soname := raw.soname,
    runpath := raw.runpath,
    segments := raw.segments,
    relocs,
    initArr,
    finiArr }

end Elf

end LeanLoad.Parse


/-
Relocation grouping for checked ELF construction.

Raw dynamic relocation tables are flat. The checked `Elf` stores relocs on the
PT_LOAD segment whose memory range contains each relocation's 8-byte write
window. This module owns that sigma-heavy bucketing; `Elf.Check` just consumes
the attached segment array.
-/

import LeanLoad.Parse.Elf.LoadMap
import LeanLoad.Parse.Reloc.Raw

namespace LeanLoad.Parse.Elf

open LeanLoad.Parse

namespace RelocBuckets

/-- A relocation paired with the checked segment index whose memory range
    contains its 8-byte write window. -/
abbrev Entry (segments : Segments) :=
  Σ i : Fin segments.items.size,
    Rela segments.items[i].phdr.p_vaddr segments.items[i].phdr.p_memsz

/-- Find the PT_LOAD index that fully covers `r`'s 8-byte write window. -/
private def locate (segments : Segments) (r : RawRela) :
    Option (Entry segments) := Id.run do
  for h : i in [:segments.items.size] do
    let idx : Fin segments.items.size := ⟨i, h.upper⟩
    let s := segments.items[idx]
    if h_lo : s.phdr.p_vaddr.toNat ≤ r.r_offset.toNat then
      if h_hi : r.r_offset.toNat + 8 ≤ s.phdr.p_vaddr.toNat + s.phdr.p_memsz.toNat then
        return some ⟨idx, { raw := r, covered := ⟨h_lo, h_hi⟩ }⟩
  return none

/-- Bucket a flat relocation table by containing checked PT_LOAD segment. -/
private def groupOne (label : String) (segments : Segments) (rs : Array RawRela) :
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
private def buildBucket (segments : Segments) (bucketIdx : Fin segments.items.size)
    (bucket : Array (Entry segments)) :
    Array (Rela segments.items[bucketIdx].phdr.p_vaddr
      segments.items[bucketIdx].phdr.p_memsz) :=
  bucket.filterMap fun ⟨i, rela⟩ =>
    if h_eq : i = bucketIdx then
      some { raw := rela.raw, covered := h_eq ▸ rela.covered }
    else none

private def attachedItems (segments : Segments)
    (relaBuckets jmprelBuckets : Array (Array (Entry segments))) :
    Array Segment :=
  Array.ofFn fun bucketIdx : Fin segments.items.size =>
    let seg := segments.items[bucketIdx]
    let rB := relaBuckets[bucketIdx.val]?.getD #[]
    let jB := jmprelBuckets[bucketIdx.val]?.getD #[]
    Segment.withRelocs seg
     (buildBucket segments bucketIdx rB)
     (buildBucket segments bucketIdx jB)

/-- Attach flat `DT_RELA` and `DT_JMPREL` tables to their checked PT_LOAD
    segments, preserving each segment's existing layout witnesses. -/
def attach (segments : Segments) (rela jmprel : Array RawRela) :
    Except String Segments := do
  let relaBuckets   ← groupOne "DT_RELA" segments rela
  let jmprelBuckets ← groupOne "DT_JMPREL" segments jmprel
  let items := attachedItems segments relaBuckets jmprelBuckets
  return {
    items,
    sorted := by
     intro i h_i j h_j h_ij
     have h_i' : i < segments.items.size := by
       simpa [items, attachedItems] using h_i
     have h_j' : j < segments.items.size := by
       simpa [items, attachedItems] using h_j
     simpa [items, attachedItems, Segment.withRelocs, Segment.vaddr] using
       segments.sorted i h_i' j h_j' h_ij,
    nonOverlap := by
     intro i h_i j h_j h_ij
     have h_i' : i < segments.items.size := by
       simpa [items, attachedItems] using h_i
     have h_j' : j < segments.items.size := by
       simpa [items, attachedItems] using h_j
     simpa [items, attachedItems, Segment.withRelocs, Segment.vaddr, Segment.memsz] using
       segments.nonOverlap i h_i' j h_j' h_ij
  }

end RelocBuckets

end LeanLoad.Parse.Elf

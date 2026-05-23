/-
Final checked ELF parser product and entry points.

`ImageView` establishes header and PT_LOAD facts, `Dynamic` reads dynamic
content through that view, and this module performs the remaining whole-ELF
checks before exposing the checked `Elf` type.
-/

import LeanLoad.Parse.Dynamic.Basic
import LeanLoad.Parse.Dynamic.InitFini
import LeanLoad.Parse.Dynamic.Symbol.Checked
import LeanLoad.Parse.Dynamic.Reloc.Raw
import LeanLoad.Parse.ImageView.Segment.Array
import LeanLoad.Runtime

namespace LeanLoad.Parse

/-- The checked form of an ELF.

    `parseM` enforces ELF-class / endian sanity, gabi-07 PT_LOAD
    well-formedness, per-rela segment containment, and init/fini target
    coverage as preconditions on construction; the `Elf` type is the witness
    that those checks passed. -/
structure Elf where
  /-- Parsed ELF header. `ElfHeader` is already semantically typed: magic,
      identifiers, `e_type`, `e_machine`, addresses, and sentinels are decoded
      to parse-layer field types. -/
  header   : ElfHeader
  symtab   : Array Symbol
  needed   : Array String
  soname   : Option String
  runpath  : Option String
  /-- Checked PT_LOAD array, in phdr order, with relas grouped by the segment
      they target and array-level ordering/disjointness witnessed. -/
  segments : Segments
  /-- `DT_INIT_ARRAY` entries — ctors, walked forward on startup. Each entry is
      zero or targets an executable PT_LOAD in `segments`. -/
  initArr  : Elf.InitFiniArray segments
  /-- `DT_FINI_ARRAY` entries — dtors, walked backward on exit. Each entry is
      zero or targets an executable PT_LOAD in `segments`. -/
  finiArr  : Elf.InitFiniArray segments
  deriving Repr

namespace Elf

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
private def attach (segments : Segments) (rela jmprel : Array RawRela) :
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
     simpa [items, attachedItems, Segment.withRelocs, Segment.eaddr] using
       segments.sorted i h_i' j h_j' h_ij,
    nonOverlap := by
     intro i h_i j h_j h_ij
     have h_i' : i < segments.items.size := by
       simpa [items, attachedItems] using h_i
     have h_j' : j < segments.items.size := by
       simpa [items, attachedItems] using h_j
     simpa [items, attachedItems, Segment.withRelocs, Segment.eaddr, Segment.memsz] using
       segments.nonOverlap i h_i' j h_j' h_ij
  }

end RelocBuckets

/-- Check a dynamic staging image into the final witness-carrying `Elf`. Header
    policy, PT_LOAD well-formedness, and dynamic string resolution are already
    carried by `Dynamic`. -/
def ofDynamic (raw : Dynamic) : Except String Elf := do
  let header := raw.header
  let segments ← RelocBuckets.attach raw.segments raw.rela raw.jmprel
  let symtab : Array Symbol ← raw.symtab.mapM (Symbol.ofRaw raw.strtab)
  let initArr ← checkInitFiniArray "DT_INIT_ARRAY" segments raw.initArr
  let finiArr ← checkInitFiniArray "DT_FINI_ARRAY" segments raw.finiArr
  return {
    header,
    symtab,
    needed := raw.needed,
    soname := raw.soname,
    runpath := raw.runpath,
    segments,
    initArr,
    finiArr }

end Elf

/-- Monad-polymorphic checked parse. The `FileReader m` abstracts byte
    delivery; all parse and validation errors flow through `ExceptT`. -/
def parseM [Monad m] (r : FileReader m) : ExceptT String m Elf := do
  let image ← Dynamic.readM r
  match Elf.ofDynamic image with
  | .ok elf  => pure elf
  | .error e => throw e

/-- Production entry point: parse and check an open file. -/
def parse (f : Runtime.File) : IO Elf := do
  match ← (parseM (Runtime.fileReader f)).run with
  | .ok elf  => pure elf
  | .error e => throw (IO.userError e)

end LeanLoad.Parse

/-
Checked dynamic relocation tables.

`RelocTable` keeps dynamic relocations flat in ELF table order while each entry
is located in a checked PT_LOAD segment by its dependent pair index.
-/

import ElfLoader.Parse.Reloc.Basic
import ElfLoader.Parse.LoadMap.Segment.Table

namespace ElfLoader.Parse

namespace Reloc

/-- Dynamic relocations located in checked load-map segments.

    The table stays flat in ELF table order, while each entry carries the
    concrete segment index and the segment-indexed `Reloc` witness. Layout can
    project the rows for one segment when building that segment's plan. -/
structure RelocTable {fileSize : ByteSize} (segments : SegmentTable fileSize) where
  rela   : Array (Σ i : Fin segments.items.size, Reloc segments.items[i])
  jmprel : Array (Σ i : Fin segments.items.size, Reloc segments.items[i])
  deriving Repr

/-- Find the PT_LOAD index that fully covers `r`'s 8-byte write window. -/
private def locate {fileSize : ByteSize} (segments : SegmentTable fileSize) (r : RawRela) :
    Option (Σ i : Fin segments.items.size, Reloc segments.items[i]) := Id.run do
  for h : i in [:segments.items.size] do
    let idx : Fin segments.items.size := ⟨i, h.upper⟩
    let s := segments.items[idx]
    if h_lo : s.eaddr.toNat ≤ r.r_offset.toNat then
      if h_hi : r.r_offset.toNat + 8 ≤ s.eaddr.toNat + s.memsz.toNat then
        return some ⟨idx, { raw := r, covered := ⟨h_lo, h_hi⟩ }⟩
  return none

/-- Locate every relocation in a flat table. -/
private def locateTable {fileSize : ByteSize} (label : String) (segments : SegmentTable fileSize)
    (rs : Array RawRela) :
    Except String (Array (Σ i : Fin segments.items.size, Reloc segments.items[i])) := do
  let mut located : Array (Σ i : Fin segments.items.size, Reloc segments.items[i]) := #[]
  for r in rs do
    match locate segments r with
    | none =>
        .error s!"parse {label}: rela r_offset=0x{r.r_offset.toNat} \
          not covered by any PT_LOAD segment"
    | some entry =>
        located := located.push entry
  return located

namespace RelocTable

/-- Project a located relocation array to one segment, preserving table order. -/
private def forSegmentFrom {fileSize : ByteSize} {segments : SegmentTable fileSize}
    (items : Array (Σ i : Fin segments.items.size, Reloc segments.items[i]))
    (segmentIdx : Fin segments.items.size) :
    Array (Reloc segments.items[segmentIdx]) :=
  items.filterMap fun ⟨i, reloc⟩ =>
    if h_eq : i = segmentIdx then
      some (h_eq ▸ reloc)
    else none

/-- `DT_RELA` entries located in `segmentIdx`. -/
def relaFor {fileSize : ByteSize} {segments : SegmentTable fileSize}
    (table : RelocTable segments) (segmentIdx : Fin segments.items.size) :
    Array (Reloc segments.items[segmentIdx]) :=
  forSegmentFrom table.rela segmentIdx

/-- `DT_JMPREL` entries located in `segmentIdx`. -/
def jmprelFor {fileSize : ByteSize} {segments : SegmentTable fileSize}
    (table : RelocTable segments) (segmentIdx : Fin segments.items.size) :
    Array (Reloc segments.items[segmentIdx]) :=
  forSegmentFrom table.jmprel segmentIdx

end RelocTable

/-- Locate flat `DT_RELA` and `DT_JMPREL` tables in their owning checked
    PT_LOAD segments. Each resulting relocation carries the segment-local
    `covered` witness that its conservative 8-byte write window belongs to
    that segment. -/
def locateAll {fileSize : ByteSize} (segments : SegmentTable fileSize) (rela jmprel : Array RawRela) :
    Except String (RelocTable segments) := do
  let rela ← locateTable "DT_RELA" segments rela
  let jmprel ← locateTable "DT_JMPREL" segments jmprel
  return { rela, jmprel }

end Reloc

end ElfLoader.Parse

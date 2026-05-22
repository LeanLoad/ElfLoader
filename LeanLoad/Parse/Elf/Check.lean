/-
Checked construction for `Parse.Elf`.

This module consumes the byte staging image from `Elf.RawImage` and establishes the
semantic witnesses carried by the public `LeanLoad.Parse.Elf` type.
-/

import LeanLoad.Parse.Elf.Checked
import LeanLoad.Parse.Elf.RawImage
import LeanLoad.Parse.Elf.Relocs

namespace LeanLoad.Parse.Elf

open LeanLoad.Parse

/-- Resolve a dynamic string-table offset while preserving diagnostic context
    for the tag that supplied it. -/
private def resolveStrtabOff (label : String) (strtab : RawStrtab) (off : StrtabOff) :
    Except String String :=
  match StrtabEntry.ofOff strtab off with
  | .ok entry => .ok entry.value
  | .error e  => .error s!"parse: {label}: {e}"

/-- Check a staging image: attach every rela to its checked PT_LOAD segment,
    pre-resolve every dynamic string-table reference, and bundle the final
    witness-carrying `Elf`. Header policy and PT_LOAD well-formedness were
    already established by `LoadMap`. -/
def checkImage (raw : RawImage) : Except String _root_.LeanLoad.Parse.Elf := do
  let header := raw.loadMap.header
  let segmentsArray ← RelocBuckets.attach raw.loadMap.segments raw.rela raw.jmprel
  let symtab : Array Symbol ← raw.symtab.mapM (Symbol.ofRaw raw.strtab)
  let needed : Array String ← raw.needed.mapM (resolveStrtabOff "DT_NEEDED" raw.strtab)
  let soname : Option String ←
    match raw.soname with
    | none     => (pure none : Except String (Option String))
    | some off => do
        let s ← resolveStrtabOff "DT_SONAME" raw.strtab off
        pure (some s)
  let runpath : Option String ←
    match raw.runpath with
    | none     => (pure none : Except String (Option String))
    | some off => do
        let s ← resolveStrtabOff "DT_RUNPATH" raw.strtab off
        pure (some s)
  match Segments.ofArray segmentsArray with
  | .ok segments =>
    let checkInitFiniArray (label : String) (entries : Array Vaddr) :
        Except String (InitFiniArray segments) := do
      let mut checked : InitFiniArray segments := #[]
      for h : i in [:entries.size] do
        let entry := entries[i]
        let decExec : Decidable (callTargetInExecSeg segments entry) := by
          unfold callTargetInExecSeg Segments.ExecAddr Segments.ContainsVaddr Segment.ContainsVaddr
          infer_instance
        match decExec with
        | .isTrue h_exec =>
            checked := checked.push ⟨entry, h_exec⟩
        | .isFalse _ =>
            .error s!"parse: {label}[{i}] = 0x{entry.toNat} is not zero or in any \
              executable PT_LOAD ({entries.size} entries total)"
      return checked
    let phdr_nbytes : Nat := Parse.RawPhdrSize * header.e_phnum.toNat
    let decPhdr : Decidable (PhdrCovered segments.items header.e_phoff phdr_nbytes) := by
      unfold PhdrCovered coversPhdrs
      infer_instance
    match decPhdr with
    | .isTrue h_phdr =>
      let initArr ← checkInitFiniArray "DT_INIT_ARRAY" raw.initArr
      let finiArr ← checkInitFiniArray "DT_FINI_ARRAY" raw.finiArr
      return {
        header,
        symtab,
        needed, soname, runpath, segments,
        initArr, finiArr,
        phdrCovered := h_phdr }
    | .isFalse _ =>
      .error s!"parse: phdr table at file offset \
        0x{header.e_phoff.toNat} (size {phdr_nbytes}) is not covered \
        by any PT_LOAD with vaddr=offset; AT_PHDR cannot be computed as \
        mainBase + phoff"
  | .error e => .error e

end LeanLoad.Parse.Elf

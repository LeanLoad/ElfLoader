/-
Checked construction for `Parse.Elf`.

This module consumes the byte staging image from `Elf.RawImage` and establishes the
semantic witnesses carried by the public `LeanLoad.Parse.Elf` type.
-/

import LeanLoad.Parse.Elf.Checked
import LeanLoad.Parse.Elf.RawImage
import LeanLoad.Parse.Elf.Relocs
import LeanLoad.Parse.Elf.InitFini

namespace LeanLoad.Parse.Elf

open LeanLoad.Parse

/-- Resolve a dynamic string-table offset while preserving diagnostic context
    for the tag that supplied it. -/
private def resolveStrtabOff (label : String) (strtab : Strtab) (off : StrtabOff) :
    Except String String :=
  match StrtabEntry.ofOff strtab off with
  | .ok entry => .ok entry.value
  | .error e  => .error s!"parse: {label}: {e}"

/-- Resolve an optional dynamic string-table reference with the tag name in
    diagnostics. -/
private def resolveStrtabOff? (label : String) (strtab : Strtab) :
    Option StrtabOff → Except String (Option String)
  | none     => .ok none
  | some off => do
      let s ← resolveStrtabOff label strtab off
      pure (some s)

/-- Check a staging image: attach every rela to its checked PT_LOAD segment,
    pre-resolve every dynamic string-table reference, and bundle the final
    witness-carrying `Elf`. Header policy and PT_LOAD well-formedness were
    already established by `LoadMap`. -/
def checkImage (raw : RawImage) : Except String _root_.LeanLoad.Parse.Elf := do
  let header := raw.loadMap.header
  let segments ← RelocBuckets.attach raw.loadMap.segments raw.rela raw.jmprel
  let symtab : Array Symbol ← raw.symtab.mapM (Symbol.ofRaw raw.strtab)
  let needed : Array String ← raw.needed.mapM (resolveStrtabOff "DT_NEEDED" raw.strtab)
  let soname ← resolveStrtabOff? "DT_SONAME" raw.strtab raw.soname
  let runpath ← resolveStrtabOff? "DT_RUNPATH" raw.strtab raw.runpath
  let initArr ← checkInitFiniArray "DT_INIT_ARRAY" segments raw.initArr
  let finiArr ← checkInitFiniArray "DT_FINI_ARRAY" segments raw.finiArr
  return {
    header,
    symtab,
    needed, soname, runpath, segments,
    initArr, finiArr }

end LeanLoad.Parse.Elf

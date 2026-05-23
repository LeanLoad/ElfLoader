/-
Checked construction for `Parse.Elf`.

This module consumes the byte staging image from `Dynamic` and establishes the
semantic witnesses carried by the public `LeanLoad.Parse.Elf` type.
-/

import LeanLoad.Parse.Elf.Checked
import LeanLoad.Parse.Dynamic.Basic
import LeanLoad.Parse.Elf.Relocs
import LeanLoad.Parse.Dynamic.InitFini

namespace LeanLoad.Parse.Elf

open LeanLoad.Parse

/-- Check a staging image: attach every rela to its checked PT_LOAD segment,
    bundle the final witness-carrying `Elf`. Header policy, PT_LOAD
    well-formedness, and dynamic string resolution are already carried by
    `Dynamic`. -/
def checkImage (raw : Dynamic) : Except String _root_.LeanLoad.Parse.Elf := do
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
    initArr, finiArr }

end LeanLoad.Parse.Elf

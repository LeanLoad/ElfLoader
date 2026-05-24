/-
Checked callable ELF-address targets for a parsed object.

`e_entry`, `DT_INIT_ARRAY`, and `DT_FINI_ARRAY` all name code addresses that
may be invoked after mapping. For LeanLoad's supported ET_DYN inputs, each
non-zero address is base-relative and must land in an executable PT_LOAD.
-/

import LeanLoad.Parse.LoadMap.SegmentTable.Basic

namespace LeanLoad.Parse

/-- A callable ELF-address slot: either zero or inside an executable PT_LOAD. -/
abbrev CallTarget (segments : SegmentTable) :=
  { addr : Eaddr // callTargetInExecSeg segments addr }

namespace CallTarget

/-- Check one raw callable address. Zero is accepted as the ELF no-op sentinel;
    non-zero addresses must target an executable PT_LOAD. -/
def ofRaw (label : String) (segments : SegmentTable) (addr : Eaddr) :
    Except String (CallTarget segments) :=
  let decExec : Decidable (callTargetInExecSeg segments addr) := by
    unfold callTargetInExecSeg SegmentTable.ExecAddr SegmentTable.ContainsEaddr
      Segment.ContainsEaddr
    infer_instance
  match decExec with
  | .isTrue h_exec => .ok ⟨addr, h_exec⟩
  | .isFalse _ =>
      .error s!"parse: {label} = 0x{addr.toNat} is not zero or in any executable PT_LOAD"

/-- Check one dynamic callable-address array, preserving table order. -/
def arrayOfRaw (label : String) (segments : SegmentTable) (addrs : Array Eaddr) :
    Except String (Array (CallTarget segments)) := do
  let mut checked : Array (CallTarget segments) := #[]
  for h : i in [:addrs.size] do
    match ofRaw s!"{label}[{i}]" segments addrs[i] with
    | .ok target => checked := checked.push target
    | .error e   => throw s!"{e} ({addrs.size} entries total)"
  return checked

end CallTarget

/-- All callable ELF-address slots attached to a parsed object.

    `entry` comes from `Elf64_Ehdr.e_entry` (gabi 04 § ELF Header). `init` and
    `fini` preserve `DT_INIT_ARRAY` / `DT_FINI_ARRAY` order (gabi 08 § Dynamic
    Section). Each slot carries the zero-or-executable-target witness. -/
structure CallTargets (segments : SegmentTable) where
  entry : CallTarget segments
  init  : Array (CallTarget segments)
  fini  : Array (CallTarget segments)
  deriving Repr

namespace CallTargets

/-- Empty/default call-target set for examples that synthesize inert ELFs. -/
def empty (segments : SegmentTable) : CallTargets segments :=
  { entry := ⟨0, Or.inl (by decide)⟩
    init := #[]
    fini := #[] }

/-- Check the raw callable addresses decoded from the ELF header and dynamic table. -/
def ofRaw (segments : SegmentTable) (entry : Eaddr)
    (init fini : Array Eaddr) : Except String (CallTargets segments) := do
  let entry ← CallTarget.ofRaw "e_entry" segments entry
  let init ← CallTarget.arrayOfRaw "DT_INIT_ARRAY" segments init
  let fini ← CallTarget.arrayOfRaw "DT_FINI_ARRAY" segments fini
  pure { entry, init, fini }

end CallTargets

#guard (CallTarget.ofRaw "e_entry" SegmentTable.empty 0).isOk
#guard (CallTarget.ofRaw "e_entry" SegmentTable.empty 1).isOk = false

#guard
  match CallTargets.ofRaw SegmentTable.empty 0 #[0] #[] with
  | .ok targets => targets.init.size == 1
  | .error _    => false

end LeanLoad.Parse

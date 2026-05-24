/-
Constructor/destructor target validation for dynamic parse data.

The byte-level reader preserves raw `DT_INIT_ARRAY` / `DT_FINI_ARRAY` order.
This module checks each decoded function pointer against the checked PT_LOAD
array carried by `Dynamic` and attaches the executable-target witness consumed
by the final `Elf`.
-/

import LeanLoad.Parse.LoadMap.SegmentTable.Basic

namespace LeanLoad.Parse

namespace Dynamic

/-- A constructor/destructor function pointer that is zero or targets an
    executable PT_LOAD in `segments`. -/
abbrev InitFiniEntry (segments : SegmentTable) :=
  { entry : Eaddr // callTargetInExecSeg segments entry }

/-- `DT_INIT_ARRAY` / `DT_FINI_ARRAY` entries. Call order is table order, while
    each entry carries the witness that it targets an executable segment. -/
abbrev InitFiniArray (segments : SegmentTable) :=
  Array (InitFiniEntry segments)

namespace InitFiniArray

/-- Check one dynamic constructor/destructor array. Zero is accepted by
    `callTargetInExecSeg`; non-zero entries must point into an executable
    PT_LOAD segment. -/
def ofRaw (label : String) (segments : SegmentTable) (entries : Array Eaddr) :
    Except String (InitFiniArray segments) := do
  let mut checked : InitFiniArray segments := #[]
  for h : i in [:entries.size] do
    let entry := entries[i]
    let decExec : Decidable (callTargetInExecSeg segments entry) := by
      unfold callTargetInExecSeg SegmentTable.ExecAddr SegmentTable.ContainsEaddr
        Segment.ContainsEaddr
      infer_instance
    match decExec with
    | .isTrue h_exec =>
        checked := checked.push ⟨entry, h_exec⟩
    | .isFalse _ =>
        .error s!"parse: {label}[{i}] = 0x{entry.toNat} is not zero or in any \
          executable PT_LOAD ({entries.size} entries total)"
  return checked

end InitFiniArray

end Dynamic

end LeanLoad.Parse

/-
Constructor/destructor target validation for checked ELF construction.

The byte-level reader preserves raw `DT_INIT_ARRAY` / `DT_FINI_ARRAY` order.
This module checks each decoded function pointer against the final checked
PT_LOAD array and attaches the executable-target witness consumed by `Elf`.
-/

import LeanLoad.Parse.ImageView.Segment.Properties

namespace LeanLoad.Parse

namespace Elf

/-- A constructor/destructor function pointer that is zero or targets an
    executable PT_LOAD in `segments`. -/
abbrev InitFiniEntry (segments : Segments) :=
  { entry : Eaddr // callTargetInExecSeg segments entry }

/-- `DT_INIT_ARRAY` / `DT_FINI_ARRAY` entries. The array is ELF-owned
    because call order is table order, while each entry carries the
    witness that it targets an executable segment. -/
abbrev InitFiniArray (segments : Segments) :=
  Array (InitFiniEntry segments)

end Elf

namespace Elf

/-- Check one dynamic constructor/destructor array. Zero is accepted by
    `callTargetInExecSeg`; non-zero entries must point into an executable
    PT_LOAD segment. -/
def checkInitFiniArray (label : String) (segments : Segments) (entries : Array Eaddr) :
    Except String (InitFiniArray segments) := do
  let mut checked : InitFiniArray segments := #[]
  for h : i in [:entries.size] do
    let entry := entries[i]
    let decExec : Decidable (callTargetInExecSeg segments entry) := by
      unfold callTargetInExecSeg Segments.ExecAddr Segments.ContainsEaddr Segment.ContainsEaddr
      infer_instance
    match decExec with
    | .isTrue h_exec =>
        checked := checked.push ⟨entry, h_exec⟩
    | .isFalse _ =>
        .error s!"parse: {label}[{i}] = 0x{entry.toNat} is not zero or in any \
          executable PT_LOAD ({entries.size} entries total)"
  return checked

end Elf

end LeanLoad.Parse

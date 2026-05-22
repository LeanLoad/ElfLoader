/-
Typed fields for `ProgramHeader`.

`p_type` is decoded into a range-aware `ProgramHeaderType`; `p_flags` is decoded
into the named gABI permission bits plus OS/proc-specific masks.

Spec: `third_party/gabi/docsrc/elf/07-pheader.rst`.
-/

import LeanLoad.Parse.Decode

namespace LeanLoad.Parse

-- Program header type: `p_type` (gabi 07 § Program Header).

/-- Program-header segment type (`p_type`).

    gABI 07 § Program Header defines named values `PT_NULL` through
    `PT_TLS`, reserves `PT_LOOS..PT_HIOS` for OS-specific semantics,
    and reserves `PT_LOPROC..PT_HIPROC` for processor-specific
    semantics. Other values are reserved for future use. -/
inductive ProgramHeaderType where
  | null
  | load
  | dynamic
  | interp
  | note
  | shlib
  | phdr
  | tls
  | osSpecific (raw : UInt32)
  | procSpecific (raw : UInt32)
  | reserved (raw : UInt32)
  deriving Repr, BEq, DecidableEq, Inhabited

instance : RawDecode ProgramHeaderType UInt32 where
  ofRaw
  | 0 => .ok .null
  | 1 => .ok .load
  | 2 => .ok .dynamic
  | 3 => .ok .interp
  | 4 => .ok .note
  | 5 => .ok .shlib
  | 6 => .ok .phdr
  | 7 => .ok .tls
  | n =>
      if 0x60000000 ≤ n.toNat ∧ n.toNat ≤ 0x6fffffff then
        .ok (.osSpecific n)
      else if 0x70000000 ≤ n.toNat ∧ n.toNat ≤ 0x7fffffff then
        .ok (.procSpecific n)
      else
        .ok (.reserved n)

/-- gABI 07 § Program Header: segment flag bitmask (`p_flags`). -/
structure ProgramHeaderFlags where
  read : Bool
  write : Bool
  exec : Bool
  /-- Bits under `PF_MASKOS`; gABI leaves their semantics OS-specific. -/
  osSpecific : UInt32
  /-- Bits under `PF_MASKPROC`; gABI leaves their semantics to the psABI. -/
  procSpecific : UInt32
  deriving Repr, BEq, DecidableEq, Inhabited

namespace ProgramHeaderFlags

def PF_X : UInt32 := 0x1       -- Execute (gABI 07 § Segment Permissions)
def PF_W : UInt32 := 0x2       -- Write (gABI 07 § Segment Permissions)
def PF_R : UInt32 := 0x4       -- Read (gABI 07 § Segment Permissions)
def PF_MASKOS : UInt32 := 0x0ff00000   -- gABI 07 § Segment Permissions
def PF_MASKPROC : UInt32 := 0xf0000000 -- gABI 07 § Segment Permissions

/-- Decode `p_flags`. Bits outside the gABI RWX/OS/proc masks are intentionally ignored. -/
def ofRaw (flags : UInt32) : ProgramHeaderFlags :=
  { read := (flags &&& PF_R) != 0
    write := (flags &&& PF_W) != 0
    exec := (flags &&& PF_X) != 0
    osSpecific := flags &&& PF_MASKOS
    procSpecific := flags &&& PF_MASKPROC }

instance : RawDecode ProgramHeaderFlags UInt32 where
  ofRaw flags := .ok (ProgramHeaderFlags.ofRaw flags)

#guard ofRaw 0x5 = { read := true, write := false, exec := true,
                     osSpecific := 0, procSpecific := 0 }
#guard (ofRaw PF_MASKOS).osSpecific = PF_MASKOS
#guard (ofRaw PF_MASKPROC).procSpecific = PF_MASKPROC

end ProgramHeaderFlags

end LeanLoad.Parse

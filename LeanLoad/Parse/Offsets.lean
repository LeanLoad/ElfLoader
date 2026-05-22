/-
Distinguished offset types for the Parse layer.

Two semantic kinds of 64-bit offset coexist throughout `parse`:

  • `Vaddr`     — virtual address as recorded in `.dynamic` /
                  `RawPhdr.p_vaddr` / etc. Translated to a file
                  offset via `Parse.vaToOffset` over PT_LOAD coverage.

  • `StrtabOff` — byte offset into the dynamic string table
                  (`.dynstr`). Consumed by `RawStrtab.lookup`.

Both are single-field wrappers over `UInt64`. They are *distinct*
nominal types — you cannot pass a `Vaddr` to a function expecting
a `StrtabOff` and vice versa, and you cannot accidentally feed a
file offset to `vaToOffset`. Wrapping is explicit (`⟨x⟩` or
`Vaddr.mk x`); numeric literals work via `OfNat`.

No coercion *into* either type from a bare `UInt64` is provided —
that would defeat the safety. Conversion *out* (`.val` / `.toNat`)
is explicit, at the boundary where a raw byte count is needed
(e.g., feeding `Runtime.pread` once a vaddr has been resolved via
`vaToOffset`).

These types live in their own file (not in `Decode.lean`) so the
parser monad primitives stay agnostic — only the semantically-typed
layer above the primitives uses them.
-/

namespace LeanLoad.Parse

/-- Virtual address as recorded in ELF (`.dynamic` tags,
    `RawPhdr.p_vaddr`, `RawRela.r_offset`, etc.). Distinct from
    `StrtabOff` and from bare `UInt64` file offsets. Translated to
    a file offset via `Parse.vaToOffset`. -/
structure Vaddr where
  val : UInt64
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

instance : OfNat Vaddr n where ofNat := ⟨UInt64.ofNat n⟩

def Vaddr.toUInt64 (v : Vaddr) : UInt64 := v.val
def Vaddr.toNat (v : Vaddr) : Nat := v.val.toNat

/-- Byte offset into the dynamic string table (`.dynstr`).
    Consumed by `RawStrtab.lookup` to recover the NUL-terminated
    name at that offset. Distinct from `Vaddr` (which indexes into
    the loaded image's virtual address space, not into the strtab
    buffer). -/
structure StrtabOff where
  val : UInt64
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

instance : OfNat StrtabOff n where ofNat := ⟨UInt64.ofNat n⟩

def StrtabOff.toUInt64 (s : StrtabOff) : UInt64 := s.val
def StrtabOff.toNat (s : StrtabOff) : Nat := s.val.toNat

end LeanLoad.Parse

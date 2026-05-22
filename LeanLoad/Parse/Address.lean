/-
Distinguished address and extent types for the Parse layer.

Several semantic kinds of parse-layer addresses, offsets, and extents coexist:

  • `Vaddr`     — virtual address as recorded in `.dynamic` /
                  `Phdr.p_vaddr` / etc. Translated to a file
                  offset via `Parse.Elf.LoadMap` over checked PT_LOAD
                  coverage.

  • `FileOff`   — byte offset in the ELF file, consumed by file reads.

  • `ByteSize`  — byte length / extent of a file or memory region.

  • `StrtabOff` — byte offset into the dynamic string table
                  (`.dynstr`). Consumed by `Strtab.lookup`.

  • `VaddrSpan` — raw `(Vaddr, ByteSize)` pair before no-wrap or
                  load-map containment has been established.

The scalar forms are single-field wrappers over `UInt64`. They are distinct
nominal types — you cannot pass a `Vaddr` to a function expecting a `FileOff`,
or a `ByteSize` where a string-table offset is required. Wrapping is explicit
(`⟨x⟩` or `Vaddr.mk x`); numeric literals work via `OfNat`.

No coercion *into* these types from a bare `UInt64` is provided — that
would defeat the safety. Conversion *out* (`.val` / `.toNat`) is
explicit, at the boundary where raw arithmetic or IO needs it.
-/

import LeanLoad.Parse.Decode

namespace LeanLoad.Parse

/-- Virtual address as recorded in ELF (`.dynamic` tags,
    `Phdr.p_vaddr`, etc.). Distinct from `FileOff` and `StrtabOff`.
    Translated to a file offset via `Parse.Elf.LoadMap`. -/
structure Vaddr where
  val : UInt64
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

instance : OfNat Vaddr n where ofNat := ⟨UInt64.ofNat n⟩

instance : RawDecode Vaddr UInt64 where ofRaw v := .ok ⟨v⟩

def Vaddr.toUInt64 (v : Vaddr) : UInt64 := v.val
def Vaddr.toNat (v : Vaddr) : Nat := v.val.toNat

/-- Byte offset in the ELF file. Distinct from `Vaddr`, which is an
    address in the loaded image's virtual address space. -/
structure FileOff where
  val : UInt64
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

instance : OfNat FileOff n where ofNat := ⟨UInt64.ofNat n⟩

instance : RawDecode FileOff UInt64 where ofRaw v := .ok ⟨v⟩

def FileOff.toUInt64 (o : FileOff) : UInt64 := o.val
def FileOff.toNat (o : FileOff) : Nat := o.val.toNat

/-- Byte length / extent of a file or memory region. -/
structure ByteSize where
  val : UInt64
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

instance : OfNat ByteSize n where ofNat := ⟨UInt64.ofNat n⟩

instance : RawDecode ByteSize UInt64 where ofRaw v := .ok ⟨v⟩

def ByteSize.toUInt64 (s : ByteSize) : UInt64 := s.val
def ByteSize.toNat (s : ByteSize) : Nat := s.val.toNat

/-- Convert arithmetic over `Nat` counts into a parser byte extent. -/
def ByteSize.ofNat (n : Nat) : ByteSize := ⟨n.toUInt64⟩

/-- Byte extent for `count` fixed-width entries. -/
def ByteSize.ofEntries (count entrySize : Nat) : ByteSize :=
  ByteSize.ofNat (count * entrySize)

/-- Effective segment layout alignment: gabi 07 § Program Header permits
    `p_align = 0`; LeanLoad's total page math treats it as alignment 1. -/
def segmentLayoutAlign (align : UInt64) : UInt64 :=
  if align == 0 then 1 else align

/-- Raw virtual-address span `[start, start + size)` before any no-wrap or
    load-map containment witness has been established. -/
structure VaddrSpan where
  start : Vaddr
  size  : ByteSize
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

/-- Half-open file-byte range `[off, off + len)` known to fit inside a file of
    observed byte size `fileSize`. This strengthens `(FileOff, ByteSize)`
    without making raw `FileOff` depend on a particular file. -/
structure FileRange (fileSize : UInt64) (off : FileOff) (len : ByteSize) where
  inFile : off.toNat + len.toNat ≤ fileSize.toNat

/-- Byte offset into the dynamic string table (`.dynstr`). Consumed by
    `Strtab.lookup` to recover the NUL-terminated name at that
    offset. Distinct from `Vaddr` and `FileOff`. -/
structure StrtabOff where
  val : UInt64
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

instance : OfNat StrtabOff n where ofNat := ⟨UInt64.ofNat n⟩

def StrtabOff.toUInt64 (s : StrtabOff) : UInt64 := s.val
def StrtabOff.toNat (s : StrtabOff) : Nat := s.val.toNat

end LeanLoad.Parse

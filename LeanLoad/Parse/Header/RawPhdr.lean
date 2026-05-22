/-
gabi 07 § Program Header — `Elf64_Phdr` entry.

Only the two `p_type` values that `Parse.RawElf.parse` uses
navigationally (find the dynamic section, find the PT_LOAD covering
an offset) are defined here. The full enumeration of `p_type` and
`p_flags` lives in `Elaborate/Segment.lean`.
-/

import LeanLoad.Parse.Decode
import LeanLoad.Parse.Deriving
import LeanLoad.Parse.Offsets

namespace LeanLoad.Parse

/-- 64-bit program header entry. Field layout matches `Elf64_Phdr`. -/
structure RawPhdr where
  p_type   : UInt32
  p_flags  : UInt32
  p_offset : UInt64
  p_vaddr  : UInt64
  p_paddr  : UInt64
  p_filesz : UInt64
  p_memsz  : UInt64
  p_align  : UInt64
  deriving Repr, Inhabited, BytesDecode

/-- Size of one `Elf64_Phdr` on disk: 4+4+8*6 = 56. -/
def RawPhdrSize : Nat := 56


-- `p_type` constants used navigationally by `Parse.RawElf.parse`.
def PT_LOAD    : UInt32 := 1
def PT_DYNAMIC : UInt32 := 2

-- ============================================================================
-- Virtual-address ↔ file-offset translation over a phdr array. Used by
-- `Parse.RawElf.parse` to read sections whose locations in the file are
-- recorded as (link-time) virtual addresses in `.dynamic`.
-- ============================================================================

/-- Per-phdr offset translation: `some off` if `ph` is a PT_LOAD
    that covers `va`, `none` otherwise. -/
private def offsetIn (va : Vaddr) (ph : RawPhdr) : Option Nat :=
  if ph.p_type == PT_LOAD ∧ ph.p_vaddr ≤ va.val ∧ va.val < ph.p_vaddr + ph.p_memsz then
    some ((va.val - ph.p_vaddr).toNat + ph.p_offset.toNat)
  else none

/-- Translate a virtual address to a file offset by walking the
    `PT_LOAD` segments. Returns `none` if no `PT_LOAD` covers `va`.
    The input is typed `Vaddr` — a file offset cannot be passed by
    mistake. -/
def vaToOffset (phdrs : Array RawPhdr) (va : Vaddr) : Option Nat :=
  phdrs.findSome? (offsetIn va)

/-- Correctness witness: a successful `vaToOffset` returns an offset
    derived from a covering PT_LOAD phdr in `phdrs`. -/
theorem vaToOffset_eq_some
    {phdrs : Array RawPhdr} {va : Vaddr} {off : Nat}
    (h : vaToOffset phdrs va = some off) :
    ∃ ph ∈ phdrs, ph.p_type = PT_LOAD ∧
                  ph.p_vaddr ≤ va.val ∧ va.val < ph.p_vaddr + ph.p_memsz ∧
                  off = (va.val - ph.p_vaddr).toNat + ph.p_offset.toNat := by
  unfold vaToOffset at h
  obtain ⟨ph, h_mem, h_some⟩ := Array.exists_of_findSome?_eq_some h
  unfold offsetIn at h_some
  split at h_some
  · rename_i hcond
    obtain ⟨h_load, h_lo, h_hi⟩ := hcond
    refine ⟨ph, h_mem, beq_iff_eq.mp h_load, h_lo, h_hi, ?_⟩
    exact (Option.some_inj.mp h_some).symm
  · contradiction

/-- 112-byte program-header fixture: one PT_LOAD covering the full
    488-byte file at `vaddr = offset = 0` (the convention every real
    linker uses so `AT_PHDR` calculations work without
    offset→vaddr translation), plus one PT_DYNAMIC pointing at the
    dynamic section at offset 0x128. Coordinated with the consolidated
    `Parse.RawElf.fixtureBytes` layout. -/
def RawPhdr.fixtureBytes : ByteArray := ⟨#[
  -- Phdr[0]: PT_LOAD covering [0..0x1e8] ────────────────────────────────
  0x01, 0x00, 0x00, 0x00,                           -- p_type   = PT_LOAD
  0x05, 0x00, 0x00, 0x00,                           -- p_flags  = R|X = 5
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_offset = 0
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_vaddr  = 0
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_paddr  = 0
  0xe8, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_filesz = 0x1e8
  0xe8, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_memsz  = 0x1e8
  0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_align  = 0x1000
  -- Phdr[1]: PT_DYNAMIC ─────────────────────────────────────────────────
  0x02, 0x00, 0x00, 0x00,                           -- p_type   = PT_DYNAMIC
  0x06, 0x00, 0x00, 0x00,                           -- p_flags  = R|W = 6
  0x28, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_offset = 0x128
  0x28, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_vaddr  = 0x128
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_paddr  = 0
  0xc0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_filesz = 0xc0
  0xc0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- p_memsz  = 0xc0
  0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00    -- p_align  = 8
]⟩

#guard RawPhdr.fixtureBytes.size == 2 * RawPhdrSize  -- = 112

section Example

open RawPhdr

private def parsedPhdrs : Option (Array RawPhdr) :=
  (Parser.run fixtureBytes (decodeArray (α := RawPhdr) 0 2)).toOption

#guard parsedPhdrs.map (·.size) = some 2
-- PT_LOAD
#guard (parsedPhdrs.bind (·[0]?)).map (·.p_type)   = some PT_LOAD
#guard (parsedPhdrs.bind (·[0]?)).map (·.p_flags)  = some 5      -- R|X
#guard (parsedPhdrs.bind (·[0]?)).map (·.p_vaddr)  = some 0
#guard (parsedPhdrs.bind (·[0]?)).map (·.p_filesz) = some 0x1e8
#guard (parsedPhdrs.bind (·[0]?)).map (·.p_align)  = some 0x1000
-- PT_DYNAMIC
#guard (parsedPhdrs.bind (·[1]?)).map (·.p_type)   = some PT_DYNAMIC
#guard (parsedPhdrs.bind (·[1]?)).map (·.p_offset) = some 0x128
#guard (parsedPhdrs.bind (·[1]?)).map (·.p_filesz) = some 0xc0

-- ── `vaToOffset` over a 2-phdr array ──────────────────────────────────
-- Two non-contiguous PT_LOADs (handcrafted, not byte-decoded) exercise
-- the `vaddr ≠ offset` case that the fixture's single PT_LOAD (with
-- `vaddr = offset = 0`) can't surface alone.
private def vaTestPhdrs : Array RawPhdr := #[
  { (default : RawPhdr) with
    p_type := PT_LOAD,
    p_vaddr := 0x1000, p_memsz := 0x1000,
    p_offset := 0x1000, p_filesz := 0x1000 },
  { (default : RawPhdr) with
    p_type := PT_LOAD,
    p_vaddr := 0x3000, p_memsz := 0x500,
    p_offset := 0x2000, p_filesz := 0x500 } ]

#guard vaToOffset vaTestPhdrs (0x1000 : Vaddr) = some 0x1000  -- first PT_LOAD, identity
#guard vaToOffset vaTestPhdrs (0x1abc : Vaddr) = some 0x1abc  -- inside first segment
#guard vaToOffset vaTestPhdrs (0x3010 : Vaddr) = some 0x2010  -- second PT_LOAD, vaddr ≠ offset
#guard vaToOffset vaTestPhdrs (0x0fff : Vaddr) = none         -- before everything
#guard vaToOffset vaTestPhdrs (0x2500 : Vaddr) = none         -- gap between segments
#guard vaToOffset vaTestPhdrs (0x3500 : Vaddr) = none         -- past the second segment

-- ── Error cases ──────────────────────────────────────────────────────
-- Truncated phdr: 20 bytes when 56 (RawPhdrSize) expected. EOF hits
-- inside the `p_offset` u64 read.
#guard
  (Parser.run (fixtureBytes.extract 0 20) (BytesDecode.decode : Parser RawPhdr)).toOption.isNone

-- `decodeArray` asking for 3 entries from a 2-entry buffer: third
-- entry hits EOF.
#guard
  (Parser.run fixtureBytes (decodeArray (α := RawPhdr) 0 3)).toOption.isNone

end Example

end LeanLoad.Parse

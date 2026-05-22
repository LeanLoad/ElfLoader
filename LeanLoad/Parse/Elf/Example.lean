/-
Integration example for `Parse/Elf`.

The fixture here demonstrates cross-section coordination: PT_DYNAMIC's
`p_offset` matches the dynamic table's actual position, DT_STRTAB's
`d_un` matches the strtab's vaddr, DT_HASH's `nchain` matches the
symtab's entry count, and so on.

Crucially, `fixture` exercises the same checked `parseM` that
production uses. Only the `FileReader` instance changes (`pureReader`
vs `Runtime.fileReader`); section offsets are discovered via
the checked `LoadMap` over the parsed phdrs.

The fixture is also engineered to satisfy checked-parse gabi-07 checks:
the lone PT_LOAD has `vaddr = offset = 0` and file-backs every dynamic
table, rela offset, and init_array entry.
-/

import LeanLoad.Parse.Elf.Entry
import LeanLoad.Parse.Ehdr.Example
import LeanLoad.Parse.Phdr.Example
import LeanLoad.Parse.Dyntab.Example

namespace LeanLoad.Parse.Elf.Example

open LeanLoad.Parse

-- ---- Per-section fixture bytes ─────────────────────────────────────────
-- The struct-typed header sections come from the header example modules.
-- Dynamic-content fixtures live beside their raw structs.
-- `hashBytes` and `initArrBytes` are raw u32/u64 arrays read inline by
-- `parseM`'s `RawSysVHash.parse` / `UInt64` array decode, so they live here.

/-- Hash section (8 bytes): `nbucket = 1`, `nchain = 2`. `parseM` reads
    only the first 8 bytes via the `RawSysVHash` decoder; the bucket/chain
    arrays a real ELF appends are unused by LeanLoad and omitted. -/
private def hashBytes : ByteArray := ⟨#[
  0x01, 0x00, 0x00, 0x00,                                       -- nbucket = 1
  0x02, 0x00, 0x00, 0x00                                        -- nchain  = 2
]⟩

/-- Init array (8 bytes): one ctor pointer at 0x100 (inside PT_LOAD's
    executable memsz, so it becomes an `InitFiniEntry`). -/
private def initArrBytes : ByteArray := ⟨#[
  0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
]⟩

/-- Hand-crafted 520-byte ET_DYN ELF used as the integration fixture.
    Concatenation of every per-section fixture in file order,
    interleaved with the non-struct-typed hash + init-array sections. -/
def fixtureBytes : ByteArray :=
  Example.ehdrBytes
    ++ Example.phdrBytes
    ++ Strtab.fixtureBytes
    ++ RawSym.fixtureBytes
    ++ hashBytes
    ++ RawRela.fixtureBytes
    ++ initArrBytes
    ++ Example.dynBytes

-- Total size: sum of each section's fixture bytes.
#guard fixtureBytes.size = 0x208                  -- 520 bytes total

/-- Pure counterpart to `Parse.parse`: built by running the same
    checked `parseM` over a `pureReader` of `fixtureBytes`. Returns
    `Except String Elf` — the same error channel production surfaces,
    just without IO wrapping. -/
def fixture : Except String _root_.LeanLoad.Parse.Elf :=
  (parseM (pureReader fixtureBytes)).run

-- ---- Cross-section coordination `#guard`s ────────────────────────────
-- Per-struct field decoding is checked standalone in each Raw*.lean.
-- Here we verify the multi-section invariants the fixture is engineered
-- to satisfy — and, because `fixture` calls the production checked
-- parser, these guards also exercise validation on a synthetic ELF.

#guard match fixture with
  | .ok r =>
       r.header.e_phnum.toNat == 2                                  -- ehdr.phnum preserved
    && r.symtab.size == 2                                           -- DT_HASH.nchain ↔ symtab entries
    && r.needed == #["libc.so.6"]                                   -- DT_NEEDED → strtab[0x01]
    && r.soname == some "mylib.so"                                  -- DT_SONAME → strtab[0x12]
    && r.runpath == some "lib"                                      -- DT_RUNPATH → strtab[0x1b]
    && r.segments.items.size == 1
    && (r.segments.items[0]?.map (·.rela.size) == some 1)
    && r.initArr.size == 1
  | .error _ => false

-- The checked segment view preserves the PT_LOAD identity layout.
#guard match fixture with
  | .ok r =>
       (r.segments.items[0]?.map (fun s => s.vaddr == 0 && s.offset == 0) == some true)
    && r.header.e_entry == 0x100
  | .error _ => false

end LeanLoad.Parse.Elf.Example

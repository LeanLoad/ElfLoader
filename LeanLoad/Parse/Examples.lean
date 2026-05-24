/-
Integration example for `Parse`.

The fixture here demonstrates cross-section coordination: PT_DYNAMIC's
`p_offset` matches the dynamic table's actual position, DT_STRTAB's
`d_un` matches the strtab's eaddr, DT_HASH's `nchain` matches the
symtab's entry count, and so on.

Crucially, `fixture` exercises the same checked `parseM` that
production uses. Only the `FileOps` instance changes; section offsets are discovered via
the checked `LoadMap` over the parsed program headers.

The fixture is also engineered to satisfy checked-parse gabi-07 checks:
the lone PT_LOAD has `eaddr = offset = 0` and file-backs every dynamic
table, rela offset, and init_array entry.
-/

import LeanLoad.Parse
import LeanLoad.Parse.LoadMap.ElfIdent.Examples
import LeanLoad.Parse.LoadMap.ElfHeader.Examples
import LeanLoad.Parse.LoadMap.ProgramHeader.Examples
import LeanLoad.Parse.Dynamic.Dyntab.Examples

namespace LeanLoad.Parse.Examples

open LeanLoad.Parse

-- ---- Per-section fixture bytes ─────────────────────────────────────────
-- The struct-typed header sections come from the header example modules.
-- Dynamic-content fixtures live beside their raw structs.
-- `hashBytes` and `initArrBytes` are raw u32/u64 arrays read inline by
-- `parseM`'s `RawSysVHash` / `UInt64` array decode, so they live here.

/-- Hash section (8 bytes): `nbucket = 1`, `nchain = 2`. `parseM` reads
    only the first 8 bytes via the `RawSysVHash` decoder; the bucket/chain
    arrays a real ELF appends are unused by LeanLoad and omitted. -/
private def hashBytes : ByteArray := ⟨#[
  0x01, 0x00, 0x00, 0x00,                                       -- nbucket = 1
  0x02, 0x00, 0x00, 0x00                                        -- nchain  = 2
]⟩

/-- Init array (8 bytes): one ctor pointer at 0x100 (inside PT_LOAD's
    executable memsz, so it becomes a checked `CallTarget`). -/
private def initArrBytes : ByteArray := ⟨#[
  0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
]⟩

/-- Hand-crafted 520-byte ET_DYN ELF used as the integration fixture.
    Concatenation of every per-section fixture in file order,
    interleaved with the non-struct-typed hash + init-array sections. -/
def fixtureBytes : ByteArray :=
  elfHeaderBytes
    ++ programHeaderBytes
    ++ Strtab.fixtureBytes
    ++ RawSym.fixtureBytes
    ++ hashBytes
    ++ RawRela.fixtureBytes
    ++ initArrBytes
    ++ dynBytes

-- Total size: sum of each section's fixture bytes.
#guard fixtureBytes.size = 0x208                  -- 520 bytes total

private def fixtureOps : Runtime.FileOps Id ByteArray :=
  { openByName := fun _ _ => none
    fileSize := fun bytes => UInt64.ofNat bytes.size
    pread := fun bytes offset len =>
      let o := offset.toNat
      let n := len.toNat
      bytes.extract o (o + n) }

/-- Pure counterpart to production parsing: built by running the same
    checked `parseM` over in-memory `fixtureBytes`. Returns
    `Except String Elf` — the same error channel production surfaces,
    just without IO wrapping. -/
def fixture : Except String Elf :=
  (parseM fixtureOps fixtureBytes).run

-- ---- Cross-section coordination `#guard`s ────────────────────────────
-- Per-struct field decoding is checked standalone in each Raw*.lean.
-- Here we verify the multi-section invariants the fixture is engineered
-- to satisfy — and, because `fixture` calls the production checked
-- driver, these guards also exercise validation on a synthetic ELF.

#guard match fixture with
  | .ok r =>
       r.header.e_phnum.toNat == 2                                  -- ehdr.phnum preserved
    && r.symtab.size == 2                                           -- DT_HASH.nchain
    && r.needed == #["libc.so.6"]                                   -- DT_NEEDED → strtab[0x01]
    && r.soname == some "mylib.so"                                  -- DT_SONAME → strtab[0x12]
    && r.runpath == some "lib"                                      -- DT_RUNPATH → strtab[0x1b]
    && r.segments.items.size == 1
    && (if h : 0 < r.segments.items.size then (r.relocs.relaFor ⟨0, h⟩).size == 1 else false)
    && r.callTargets.entry.val == 0x100
    && r.callTargets.init.size == 1
  | .error _ => false

-- The checked segment view preserves the PT_LOAD identity layout.
#guard match fixture with
  | .ok r =>
       (r.segments.items[0]?.map (fun s => s.eaddr == 0 && s.offset == 0) == some true)
    && r.header.e_entry == 0x100
  | .error _ => false

end LeanLoad.Parse.Examples

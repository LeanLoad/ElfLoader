/-
`LeanLoad.Load` — IO orchestration.

The single trusted module that ties the verified core (`Parse`, `Link`)
to the FFI layer (`runtime/`). Verified code (`Parse/`, `Link/`) must
not import `LeanLoad.FFI`; everything that crosses into the kernel
goes through here.

The pipeline is uniform: every load is `Discover` → `Link` (Layout +
Init) → `realize` → `Exec.run`. A static binary with no `DT_NEEDED`
yields a single-object closure, which is just the N=1 case of the
multi-object pipeline.
-/

import LeanLoad.Common
import LeanLoad.Parse
import LeanLoad.Link
import LeanLoad.Discover
import LeanLoad.FFI

namespace LeanLoad.Load

open LeanLoad
open LeanLoad.FFI

-- ============================================================================
-- Loaded image handle
-- ============================================================================

/-- A `Handle` owns the materialised regions of a loaded binary. As
    long as the handle is reachable, the regions stay mapped. -/
structure Handle where
  regions : Array Region.Region
  entry   : UInt64

-- ============================================================================
-- Mapping materialisation
-- ============================================================================

/-- mmap a planned mapping writable, copy bytes, then mprotect to its
    final permissions. (`mprotect` to `PROT_EXEC` also flushes the
    instruction cache, which AArch64 needs.) -/
def materializeMapping (bytes : ByteArray) (m : Link.Layout.Mapping) : IO Region.Region := do
  let region ← Region.mmap m.vaddr m.length.toUSize
                 (Region.PROT_READ ||| Region.PROT_WRITE)
                 (Region.MAP_PRIVATE ||| Region.MAP_ANONYMOUS ||| Region.MAP_FIXED)
  if m.fileLen > 0 then
    let src := bytes.extract m.fileOff.toNat (m.fileOff.toNat + m.fileLen.toNat)
    Region.write region m.pageInset.toUSize src
  Region.mprotect region m.prot
  return region

/-- Materialise an `ObjectLayout` into a live array of regions. -/
def materializeObject (bytes : ByteArray) (lyt : Link.Layout.ObjectLayout)
    : IO (Array Region.Region) := do
  let mut regions := Array.mkEmpty lyt.mappings.size
  for m in lyt.mappings do
    regions := regions.push (← materializeMapping bytes m)
  return regions

/-- Materialise the main object of a `LoaderPlan` into a `Handle`.
    Single-object path; multi-object case is `materializeAll` below. -/
def realize (cl : Discover.Closure) (plan : Link.Layout.LoaderPlan) : IO Handle := do
  let some main := plan.layouts[0]?
    | throw (IO.userError "realize: empty plan")
  let some mainObj := cl.objects[main.objectIdx]?
    | throw (IO.userError "realize: missing object 0")
  let regions ← materializeObject mainObj.elf.bytes main
  let entry := main.entry.getD 0
  return { regions, entry }

-- ============================================================================
-- Multi-object materialisation (Phase 5)
--
-- Each object becomes ONE big mmap region (anonymous, RW initially)
-- of size = max(mapping.vaddr + mapping.length). Bytes are written
-- per mapping at offset = mapping.vaddr. Final permissions are
-- applied per mapping via `mprotectRange`. The kernel picks the base
-- for `ET_DYN` (PIE) objects, which is what we want.
-- ============================================================================

/-- Compute the contiguous span an object's mappings need. -/
def objectSpan (lyt : Link.Layout.ObjectLayout) : UInt64 := Id.run do
  let mut maxEnd : UInt64 := 0
  for m in lyt.mappings do
    let endAddr := m.vaddr + m.length
    if endAddr > maxEnd then maxEnd := endAddr
  return maxEnd

/-- Materialise one object as a single contiguous region. Returns the
    region handle and its base address. -/
def materializeObjectContiguous (bytes : ByteArray) (lyt : Link.Layout.ObjectLayout)
    : IO (Region.Region × UInt64) := do
  let span := objectSpan lyt
  -- One big anonymous region, RW for now, kernel picks base.
  let region ← Region.mmap 0 span.toUSize
                 (Region.PROT_READ ||| Region.PROT_WRITE)
                 (Region.MAP_PRIVATE ||| Region.MAP_ANONYMOUS)
  let base := Region.base region
  -- Copy each mapping's file bytes at its relative `vaddr + pageInset`.
  for m in lyt.mappings do
    if m.fileLen > 0 then
      let src := bytes.extract m.fileOff.toNat (m.fileOff.toNat + m.fileLen.toNat)
      Region.write region (m.vaddr + m.pageInset).toUSize src
  -- Apply final permissions per mapping.
  for m in lyt.mappings do
    Region.mprotectRange region m.vaddr.toUSize m.length.toUSize m.prot
  return (region, base)

/-- Materialise every object in a closure into one big region per
    object. Returns the regions (for keep-alive) and the chosen bases. -/
def materializeAll (cl : Discover.Closure) (plan : Link.Layout.LoaderPlan)
    : IO (Array Region.Region × Link.Reloc.Bases) := do
  let mut regions : Array Region.Region := Array.mkEmpty plan.layouts.size
  let mut bases : Link.Reloc.Bases := Array.mkEmpty plan.layouts.size
  for lyt in plan.layouts do
    let some obj := cl.objects[lyt.objectIdx]?
      | throw (IO.userError s!"materializeAll: missing object {lyt.objectIdx}")
    let (region, base) ← materializeObjectContiguous obj.elf.bytes lyt
    regions := regions.push region
    bases := bases.push base
  return (regions, bases)

-- ============================================================================
-- Relocation application
-- ============================================================================

/-- Apply one `RelocWrite` to its target object's region. The target VA
    is absolute; we subtract the chosen base to get the offset within
    the contiguous per-object region. -/
def applyReloc (regions : Array Region.Region) (bases : Link.Reloc.Bases)
    (w : Link.Reloc.RelocWrite) : IO Unit := do
  let some region := regions[w.objectIdx]?
    | throw (IO.userError s!"applyReloc: missing region {w.objectIdx}")
  let some base := bases[w.objectIdx]?
    | throw (IO.userError s!"applyReloc: missing base {w.objectIdx}")
  let offset := (w.targetVa - base).toUSize
  let bytes ←
    if w.size = 8 then pure (UInt64.toLEBytes w.value)
    else if w.size = 4 then pure (UInt64.toLEBytes32 w.value)
    else throw (IO.userError s!"applyReloc: unsupported width {w.size}")
  Region.write region offset bytes

/-- Apply every relocation. -/
def applyAllRelocs (regions : Array Region.Region) (bases : Link.Reloc.Bases)
    (writes : Array Link.Reloc.RelocWrite) : IO Unit := do
  for w in writes do
    applyReloc regions bases w

-- ============================================================================
-- Init / fini invocation
-- ============================================================================

/-- Call every entry of one object's `DT_INIT_ARRAY`. The entries were
    parsed from the file bytes; for `ET_DYN` (PIE) we add the chosen
    base to get the absolute address, for `ET_EXEC` the entry is
    already absolute. -/
def runObjectInits (cl : Discover.Closure) (bases : Link.Reloc.Bases)
    (objectIdx : Nat) : IO Unit := do
  let some obj := cl.objects[objectIdx]? | return ()
  let some base := bases[objectIdx]? | return ()
  -- ET_EXEC = 2 (gabi 02): absolute. Anything else (ET_DYN, ET_REL)
  -- is base-relative.
  let isExec := obj.elf.header.e_type = 2
  for entry in obj.elf.initArr do
    let fnAddr := if isExec then entry else base + entry
    if fnAddr != 0 then
      Exec.callCtor fnAddr

/-- Walk `initOrder` and run shared-library constructors. We **skip
    main** (`initOrder` ends with index 0): main's own `init_array`
    is invoked by `_start_c` after we transfer control. -/
def runInits (cl : Discover.Closure) (bases : Link.Reloc.Bases)
    (plan : Link.Layout.LoaderPlan) : IO Unit := do
  for objectIdx in plan.initOrder do
    if objectIdx = 0 then continue  -- main's _start_c handles its own
    runObjectInits cl bases objectIdx

-- ============================================================================
-- Build the plan + run
-- ============================================================================

/-- Stack region size for the loaded program. -/
def stackBytes : USize := 65536

/-- Plan a closure: layouts + init/fini orders. -/
def planFor (cl : Discover.Closure) : Link.Layout.LoaderPlan :=
  Link.Layout.fromClosure cl
    (Link.Init.initOrder cl)
    (Link.Init.finiOrder cl)

/-- Pick the architecture-specific relocation formula based on `e_machine`. -/
def formulaFor (machine : UInt32) : Link.Reloc.Formula :=
  -- 183 = EM_AARCH64. We commit to AArch64 for now per design.md
  -- caveats; x86-64 (62) is a future extension.
  if machine = 183 then Link.Reloc.Aarch64.formula
  else Link.Reloc.Aarch64.formula  -- fallback; ABI-incorrect for non-aarch64 but won't crash

/-- AArch64 program-header entry size (gabi 07: `Elf64_Phdr` is 56 B). -/
def phdrEntrySize : UInt64 := 56

/-- Compute auxv values that depend on the main object's runtime base
    and program-header table. Returns `(phdrVa, phnum, baseAdj)`. -/
def auxvFor (mainElf : Parse.File.ParsedElf) (mainBase : UInt64)
    : UInt64 × UInt64 × UInt64 :=
  -- `e_phoff` is a file offset; for `ET_DYN` the program-header table
  -- lives inside the first PT_LOAD, so its runtime address is
  -- `base + e_phoff`. For `ET_EXEC` (base = 0) it equals `e_phoff`.
  let phdrVa := mainBase + mainElf.header.e_phoff
  let phnum  := mainElf.header.e_phnum.toUInt64
  (phdrVa, phnum, 0)  -- AT_BASE is the dynamic linker's base; we are it.

/-- Static / single-object load. -/
def loadStatic (cl : Discover.Closure) (plan : Link.Layout.LoaderPlan) (path : String)
    : IO Unit := do
  let h ← realize cl plan
  let stack ← Region.mmap 0 stackBytes
                (Region.PROT_READ ||| Region.PROT_WRITE)
                (Region.MAP_PRIVATE ||| Region.MAP_ANONYMOUS)
  let some mainObj := cl.objects[0]?
    | throw (IO.userError "loadStatic: empty closure")
  let (phdrVa, phnum, baseVa) := auxvFor mainObj.elf 0  -- ET_EXEC base = 0
  Exec.run h.entry phdrVa phdrEntrySize phnum baseVa stack path

/-- Dynamic load: multi-object closure, materialise all, apply
    relocations, jump to main's `_start`. **Does not return.**

    Caveats (Phase 5 work in progress):
    - Init/fini arrays are NOT invoked here; the loaded `_start_c`
      handles main's own, but shared libraries' constructors are
      currently skipped.
    - The kernel-style stack is minimal (`AT_NULL` only); programs
      that read `AT_RANDOM`/`AT_PHDR` won't see them. -/
def loadDynamic (cl : Discover.Closure) (plan : Link.Layout.LoaderPlan) (path : String)
    : IO Unit := do
  let (regions, bases) ← materializeAll cl plan
  let rt := Link.Resolve.buildTable cl
  let some mainObj := cl.objects[0]?
    | throw (IO.userError "loadDynamic: empty closure")
  let formula := formulaFor mainObj.elf.header.e_machine.toUInt32
  let writes := Link.Reloc.plan formula cl bases rt
  applyAllRelocs regions bases writes
  -- Run shared-library constructors (init_array of every object except
  -- main; main's `_start_c` handles its own).
  runInits cl bases plan
  let some mainBase := bases[0]?
    | throw (IO.userError "loadDynamic: missing main base")
  let some mainLayout := plan.layouts[0]?
    | throw (IO.userError "loadDynamic: empty plan")
  let entry := mainBase + mainLayout.entry.getD 0
  let (phdrVa, phnum, baseVa) := auxvFor mainObj.elf mainBase
  let stack ← Region.mmap 0 stackBytes
                (Region.PROT_READ ||| Region.PROT_WRITE)
                (Region.MAP_PRIVATE ||| Region.MAP_ANONYMOUS)
  Exec.run entry phdrVa phdrEntrySize phnum baseVa stack path

/-- Discover + plan + materialise + jump. **Does not return.**
    Picks the static or dynamic path based on closure size. -/
def load (path : String) : IO Unit := do
  let cl ← Discover.discover path
  let plan := planFor cl
  if cl.objects.size = 1 then
    loadStatic cl plan path
  else
    loadDynamic cl plan path

-- ============================================================================
-- --inspect: print the plan, do not run
-- ============================================================================

def inspect (path : String) : IO Unit := do
  let cl ← Discover.discover path
  let plan := planFor cl
  IO.println s!"objects: {plan.layouts.size}"
  for lyt in plan.layouts do
    let some obj := cl.objects[lyt.objectIdx]? | continue
    IO.println s!"  [{lyt.objectIdx}] {obj.name} ({lyt.mappings.size} mappings)"
    if let some e := lyt.entry then
      IO.println s!"    entry: 0x{LeanLoad.Nat.hex e.toNat}"
    for m in lyt.mappings do
      IO.println s!"    vaddr=0x{LeanLoad.Nat.hex m.vaddr.toNat} len=0x{LeanLoad.Nat.hex m.length.toNat} prot={m.prot}"
  IO.println s!"init order: {plan.initOrder}"
  IO.println s!"fini order: {plan.finiOrder}"

end LeanLoad.Load

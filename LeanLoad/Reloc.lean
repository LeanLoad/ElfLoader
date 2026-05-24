/-
Relocation planning — base-free.

This stage walks checked dynamic relocation records, resolves only the symbols
those records reference, and produces base-free relocation entries. Layout later
attaches those entries to `SegmentLayout`; Finalize later bakes them into concrete
`StoreOp`s after the kernel has chosen a reservation base.

Phase split:

  1. **Reloc** (this file) — `RawRela → Entry objCount seg`. Resolves the
     symbol reference into a `Target` (three explicit cases:
     `noSymbol`, `weakUnresolved`, `resolved ref`) and bundles it with
     the rela's `type` / `r_offset` / `addend` and the inherited
     `Reloc.covered` witness. *Base-free*: no field knows about an mmap
     base.
  2. **Layout** — consumes a `Reloc.Result` and puts the planned entries on
     each `SegmentLayout.relocs`.
  2. **Bake** (`Finalize/Reloc.lean`) — `Entry objCount seg + base →
     Option StoreOp`. Computes the absolute place and symbol value once
     a reservation base is chosen, then turns each entry into a
     4-or-8-byte `StoreOp`. Used by `Finalize.buildSegment`.

The split exists because the runtime picks the per-elf base
(`Runtime.MemoryOps.reserve`) between phases 1 and 2; phase 1 is pure and runs
ahead of any IO.

Key types:
  • `Target objCount` — 3-case inductive replacing the old
    `Option (SymRef objCount)`. Lets `Main.debug` distinguish "no symbol"
    from "weak-unresolved" diagnostically; `Finalize.bakeReloc`
    collapses both unresolved cases via `Target.symRef?`.
  • `Entry objCount seg` — parameterised by the owning `Segment` so
    the `Reloc.covered` segment-containment witness from
    `Dynamic.Reloc.RelocTable` propagates forward into the
    planned tree. `SegmentOps.storesInRange` reads this witness
    structurally (via `BoundPlan.segment_storeRange_in_rsv`).

`Result.ofGraph` validates every relocation-bearing segment up front; the
`Result.entries` projection is total because `Result`'s constructor is private.
-/

import LeanLoad.Discover.Graph
import LeanLoad.Reloc.Symbol
import LeanLoad.Reloc.ABI
import LeanLoad.Parse

namespace LeanLoad.Reloc

open LeanLoad
open LeanLoad.Discover (LoadGraph)
open LeanLoad.Parse (Elf RawRela Segment Eaddr)

-- ============================================================================
-- Entry — one rela's planning result. Base-free.
-- Parameterised by the owning segment so the `Reloc.covered` witness
-- (inherited from `Dynamic.Reloc.RelocTable`) can be
-- preserved through planning. `SegmentOps.storesInRange` needs
-- `r_offset + 8 ≤ seg.eaddr + seg.memsz` to discharge structurally.
-- ============================================================================

/-- Resolution outcome for one rela's symbol reference. Three
    explicit cases collapse the old `Option (SymRef objCount)` to a richer
    discriminator so `Main.debug` can distinguish "no symbol"
    from "weak-undefined" diagnostically, and so `Finalize.bakeReloc`
    pattern-matches without an outer `Option`. All three cases drive
    `S = 0` in the formula except `resolved`. -/
inductive Target (objCount : Nat) where
  /-- `r.sym = 0` (`R_*_NONE` and similar). No symbol referenced. -/
  | noSymbol
  /-- Symbol is undef-weak and BFS returned no provider. gabi 05
      binds `S = 0`. -/
  | weakUnresolved
  /-- Symbol resolved: either locally defined or by BFS over the dependency graph. -/
  | resolved (ref : Reloc.Symbol.SymRef objCount)
  deriving Repr

namespace Target

/-- Extract the resolved provider, if any. Used by the bake step
    where both `noSymbol` and `weakUnresolved` collapse to `S = 0`. -/
def symRef? : Target objCount → Option (Reloc.Symbol.SymRef objCount)
  | .resolved ref => some ref
  | _             => none

/-- Human-readable tag for diagnostics. -/
def tag : Target objCount → String
  | .noSymbol       => "none"
  | .weakUnresolved => "weak"
  | .resolved _     => "ok"

end Target

/-- One planned relocation, owned by `seg`. `target` discriminates the
    three resolution outcomes (no symbol / weak unresolved / resolved
    provider). `Finalize.bakeReloc` collapses the two unresolved
    cases to `S = 0`. The `covered` witness carries the 8-byte-window
    containment from the parent segment forward into the planned tree. -/
structure Entry (objCount : Nat) (seg : Segment) where
  /-- Per-arch relocation type (`R_*`); the low 32 bits of `r_info`. -/
  type     : UInt32
  /-- Segment-relative byte offset for the patch. The absolute address
      `base + r_offset` is computed at exec time. -/
  r_offset : Eaddr
  /-- Addend `A` (gabi `r_addend`; bit pattern of a signed sxword). -/
  addend   : UInt64
  /-- Resolution outcome — see `Target`. -/
  target   : Target objCount
  /-- 8-byte write window fits in `[seg.eaddr, seg.eaddr + seg.memsz)`.
      Inherited from the checked `Reloc.covered` field on `Dynamic.Reloc.RelocTable`;
      preserved through `planOne` so the
      exec builder can prove `StoresContained` structurally. -/
  covered  : seg.eaddr.toNat ≤ r_offset.toNat ∧
    r_offset.toNat + 8 ≤ seg.eaddr.toNat + seg.memsz.toNat

-- ============================================================================
-- Symbol target resolution. Base-free.
-- ============================================================================

/-- Resolve which `(objectIdx, symIdx)` provides the symbol value `S`.
    Local-defined symbols stay in the referrer; undefined references resolve by
    BFS over the discovered dependency graph. Only symbols referenced by
    relocation records go through this function. -/
private def resolveTarget (g : LoadGraph) (order : Array (Fin g.objects.size))
    (objectIdx : Fin g.objects.size) (symIdx : Nat) :
    Except String (Target g.objects.size) := do
  match g.objects[objectIdx].elf.symtab[symIdx]? with
  | none =>
      .error s!"reloc: object[{objectIdx.val}]={g.objects[objectIdx].name} \
        references dynsym[{symIdx}], but dynsym has \
        {g.objects[objectIdx].elf.symtab.size} entries"
  | some entry =>
      if !entry.isUndef then
        return .resolved ⟨objectIdx, symIdx⟩
      else if entry.name == "" then
        if entry.isWeak then
          return .weakUnresolved
        else
          .error s!"reloc: object[{objectIdx.val}]={g.objects[objectIdx].name} \
            references unnamed strong-undefined dynsym[{symIdx}]"
      else
        match Reloc.Symbol.resolveByName g order entry.name with
        | some ref => return .resolved ref
        | none =>
            if entry.isWeak then
              return .weakUnresolved
            else
              .error s!"reloc: object[{objectIdx.val}]={g.objects[objectIdx].name} \
                has unresolved strong symbol '{entry.name}' at dynsym[{symIdx}]"

/-- Plan one rela: resolve target, preserve the `Reloc.covered` witness
    from the parent segment. -/
def planOne (g : LoadGraph) (order : Array (Fin g.objects.size))
    (objectIdx : Fin g.objects.size) (seg : Segment) (r : RawRela)
    (h_cov : seg.eaddr.toNat ≤ r.r_offset.toNat ∧
      r.r_offset.toNat + 8 ≤ seg.eaddr.toNat + seg.memsz.toNat) :
    Except String (Entry g.objects.size seg) := do
  let target : Target g.objects.size ←
    if r.sym == 0 then
      pure .noSymbol
    else
      resolveTarget g order objectIdx r.sym.toNat
  let entry : Entry g.objects.size seg :=
    { type := r.type,
      r_offset := r.r_offset,
      addend := r.r_addend,
      target := target,
      covered := h_cov }
  return entry

/-- Plan one segment's relas (then jmprel — both go through the same
    formula at exec time). Used by `Layout.Basic` when
    constructing each `SegmentLayout`. The `Reloc.covered` witness on each
    `Dynamic.Reloc.RelocTable` entry is threaded into the planned `Entry`'s
    `covered` field. -/
def planSegment (g : LoadGraph) (order : Array (Fin g.objects.size))
    (objectIdx : Fin g.objects.size)
    (segmentIdx : Fin g.objects[objectIdx].elf.segments.items.size) :
    Except String (Array (Entry g.objects.size
      (g.objects[objectIdx].elf.segments.items[segmentIdx]))) := do
  let relocs := g.objects[objectIdx].elf.relocs
  let seg := g.objects[objectIdx].elf.segments.items[segmentIdx]
  let mut acc : Array (Entry g.objects.size seg) := #[]
  for entry in relocs.relaFor segmentIdx do
    acc := acc.push (← planOne g order objectIdx seg entry.raw entry.covered)
  for entry in relocs.jmprelFor segmentIdx do
    acc := acc.push (← planOne g order objectIdx seg entry.raw entry.covered)
  return acc

/-- Base-free relocation plan for a discovered graph. The constructor is private:
    callers use `Result.ofGraph`, which validates every segment's relocation records
    before exposing total `entries`. -/
structure Result where
  private mk ::
  graph : LoadGraph
  order : Array (Fin graph.objects.size)
  segmentRelocs :
    (i : Fin graph.objects.size) →
    (j : Fin graph.objects[i].elf.segments.items.size) →
      Except String (Array (Entry graph.objects.size (graph.objects[i].elf.segments.items[j])))

namespace Result

/-- Number of loaded objects. -/
abbrev objCount (p : Result) : Nat := p.graph.objects.size

/-- Project the elf array of the discovered object list. -/
def objectElfs (p : Result) : Array Elf :=
  p.graph.objects.map (·.elf)

theorem objectElfs_size (p : Result) :
    p.objectElfs.size = p.graph.objects.size := by
  unfold objectElfs; simp

/-- Per-arch relocation formula, picked off the main elf's `e_machine`. -/
def formula (p : Result) : Reloc.ABI.Formula :=
  Reloc.ABI.formulaFor p.graph.main.elf.header.e_machine

/-- Fallible segment entries. Mostly useful for diagnostics; `entries` is the
    total projection for consumers after `Result.ofGraph` validation. -/
def segment (p : Result) (i : Fin p.graph.objects.size)
    (j : Fin p.graph.objects[i].elf.segments.items.size) :
    Except String (Array (Entry p.graph.objects.size (p.graph.objects[i].elf.segments.items[j]))) :=
  p.segmentRelocs i j

/-- Total entries for a checked segment. The `.error` branch is unreachable for
    values produced by `Result.ofGraph`; the constructor is private so external code
    cannot manufacture an unchecked plan. -/
def entries (p : Result) (i : Fin p.graph.objects.size)
    (j : Fin p.graph.objects[i].elf.segments.items.size) :
    Array (Entry p.graph.objects.size (p.graph.objects[i].elf.segments.items[j])) :=
  match p.segment i j with
  | .ok entries => entries
  | .error _ => #[]

/-- Build and validate the relocation plan for a discovered graph. -/
def ofGraph (g : LoadGraph) : Except String Result := do
  let order := Reloc.Symbol.bfsOrder g
  let segmentRelocs :=
    fun (i : Fin g.objects.size) (j : Fin g.objects[i].elf.segments.items.size) =>
      planSegment g order i j
  let result : Result := { graph := g, order, segmentRelocs }
  for h : i in [:g.objects.size] do
    let objectIdx : Fin g.objects.size := ⟨i, h.upper⟩
    for h_seg : j in [:g.objects[objectIdx].elf.segments.items.size] do
      let segIdx : Fin g.objects[objectIdx].elf.segments.items.size := ⟨j, h_seg.upper⟩
      match result.segment objectIdx segIdx with
      | .ok _ => pure ()
      | .error e => .error e
  return result

end Result

end LeanLoad.Reloc

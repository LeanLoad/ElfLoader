/-
LeanLoad CLI + IO orchestration.

`main` is the binary entry point; everything else in this file is
glue that ties the invariant-carrying core (`Parse` + `Discover` + `Reloc` +
`Layout` + `Finalize`) to the IO layer (`Runtime`).

The IO bookend `realize` (below) is a thin wrapper:
`Finalize.build` produces an intrinsic-safe `LoadOps`,
`Runtime.Run` dispatches it to externs,
then the one-shot finalizers (`mmapAnon` for the stack +
`execAndJump`) transfer control. Doesn't return.
-/

import LeanLoad

namespace Main

open LeanLoad

private abbrev CliM := ExceptT String IO

/-- Production object finder: C-side search/open/read plus Lean-side checked parse. -/
private def objectFinder : Discover.ObjectFinder CliM :=
  { findMain := fun mainPath => do
      match ← Runtime.File.openByName mainPath none with
      | none => throw s!"discover: cannot open main '{mainPath}'"
      | some mainFile => do
        let mainElf ← Parse.parseFile mainFile
        pure (Discover.LoadedObject.ofMain mainPath mainFile mainElf)
    findDependency := fun work => do
      match ← Runtime.File.openByName work.needed work.runpath with
      | none => pure none
      | some file => do
        let elf ← Parse.parseFile file
        match elf.soname with
        | some name => pure (some { name, handle := file, elf })
        | none      => throw s!"discover: '{work.needed}' is missing DT_SONAME (cannot dedup)" }

/-- Stack size for the loaded program. Matches musl's default (8 MiB). -/
private def stackBytes : UInt64 := 8 * 1024 * 1024

/-- Run all finalized ops inside the kernel-picked reservation,
    allocate the kernel-style stack, and `execAndJump` to entry.
    **Does not return.** -/
private def realize (bp : Finalize.BoundPlan)
    (lo : Finalize.LoadOps bp.rsv.addr bp.rsv.len bp.objCount)
    (ctorAddrs : Array UInt64) (path : String) : CliM Unit := do
  let mainElf := bp.graph.main.elf
  let mainBase := bp.mainBase
  let programHeaderNbytes : Nat := Parse.ProgramHeaderSize * mainElf.header.e_phnum.toNat
  let programHeaderMap ←
    Parse.ProgramHeaderMap.ofSegments mainElf.segments mainElf.header.e_phoff programHeaderNbytes
  let entry  := mainBase + mainElf.callTargets.entry.val.val
  let programHeaderVa := mainBase + programHeaderMap.eaddr.val
  let _ ← (Runtime.runLoadOps Runtime.Memory.io lo : IO Unit)
  -- Ctors run after the address space is fully realized — they're
  -- user code, not load ops.
  let _ ← (ctorAddrs.forM Runtime.callCtor : IO Unit)
  let stack ← Runtime.Memory.io.reserve stackBytes
  let phnum  := mainElf.header.e_phnum.toUInt64
  let phent  := Parse.ProgramHeaderSize.toUInt64
  let _ ← (Runtime.execAndJump
    { entry
      programHeaderVa
      phent
      phnum
      baseVa := 0
      stackVa := stack.val.addr
      stackLen := stack.val.len
      argv0 := path } : IO Unit)
  pure ()

/-- Right-pad a string to `objCount` chars with `c`. -/
private def padR (s : String) (objCount : Nat) (c : Char := ' ') : String :=
  s ++ String.ofList (List.replicate (objCount - s.length) c)

/-- Left-pad a string to `objCount` chars with `c`. -/
private def padL (s : String) (objCount : Nat) (c : Char := ' ') : String :=
  String.ofList (List.replicate (objCount - s.length) c) ++ s

/-- Lower-case hex string of a `Nat`, no `0x` prefix. -/
private def Nat.hex (objCount : Nat) : String :=
  String.ofList (Nat.toDigits 16 objCount)

/-- Lower-case hex, zero-padded to 12 digits (covers x86-64
    user-space addresses, which fit in 48 bits / 12 nibbles). -/
private def Nat.hex12 (objCount : Nat) : String :=
  padL (Nat.hex objCount) 12 '0'

#guard Nat.hex 0 = "0"
#guard Nat.hex 0x4000b0 = "4000b0"
#guard Nat.hex 0xdeadbeef = "deadbeef"
#guard Nat.hex12 0 = "000000000000"
#guard Nat.hex12 0x7ffffec55d68 = "7ffffec55d68"
#guard padR "abc" 6 '.' = "abc..."
#guard padL "abc" 6 '.' = "...abc"

/-- Discover (monadic core via CLI object finder) → Reloc (resolve referenced
    relocation symbols) → Layout → kernel-picked reservation → Finalize → realize.
    **Does not return.** -/
def load (path : String) : CliM Unit := do
  let discovery ← Discover.discover objectFinder 4096 path
  let relocPlan ← Reloc.Result.ofDiscover discovery
  let layout ← Layout.Layout.ofRelocResult relocPlan
  let rsvW ← Runtime.Memory.io.reserve layout.totalSpan
  let bp : Finalize.BoundPlan :=
    { relocPlan with layout, rsv := rsvW.val, h_total := rsvW.property }
  let witnessed ← Finalize.build bp
  let ctorAddrs := Finalize.ctorAddrs bp
  realize bp witnessed ctorAddrs path

/-- `--debug`: same as `load` but with a stage-by-stage summary on
    stderr. Like `load`, this transfers control and does not return. -/
def debug (path : String) : CliM Unit := do
  IO.eprintln "== 1. Discover (DFS over DT_NEEDED) =="
  let discovery ← Discover.discover objectFinder 4096 path
  let g := discovery.graph
  for obj in g.objects do
    IO.eprintln s!"  {obj.name}"

  IO.eprintln "\n== 2. Parse (per-object checked Elf views) =="
  for h : i in [:g.objects.size] do
    let obj := g.objects[i]
    let elf := obj.elf
    IO.eprintln s!"[{i}] {obj.name}"
    IO.eprintln s!"  elfType    = {repr elf.header.e_type}"
    IO.eprintln s!"  machine    = {repr elf.header.e_machine}"
    IO.eprintln s!"  entry      = 0x{Nat.hex elf.callTargets.entry.val.toNat}"
    IO.eprintln s!"  phnum      = {elf.header.e_phnum}"
    if let some sn := elf.soname  then IO.eprintln s!"  soname     = {sn}"
    if let some rp := elf.runpath then IO.eprintln s!"  runpath    = {rp}"
    if !elf.needed.isEmpty then
      IO.eprintln s!"  needed     = {elf.needed}"
    IO.eprintln s!"  symtab     = {elf.symtab.size} entries"
    IO.eprintln s!"  init      = {elf.callTargets.init.size} ctor(s)"
    IO.eprintln s!"  fini      = {elf.callTargets.fini.size} dtor(s)"
    IO.eprintln s!"  segments   ({elf.segments.items.size}):"
    for h2 : segI in [:elf.segments.items.size] do
      let seg := elf.segments.items[segI]
      let segIdx : Fin elf.segments.items.size := ⟨segI, h2.upper⟩
      let relocs := elf.relocs.relaFor segIdx
      let jmprel := elf.relocs.jmprelFor segIdx
      let prot := reprStr seg.perm
      IO.eprintln s!"    [{segI}] eaddr=0x{Nat.hex12 seg.eaddr.toNat} \
        offset=0x{Nat.hex seg.offset.toNat} \
        filesz=0x{Nat.hex seg.filesz.toNat} \
        memsz=0x{Nat.hex seg.memsz.toNat} \
        prot={prot}  rela={relocs.size}  jmprel={jmprel.size}"

  -- One-shot pure-pipeline build. Reloc resolves only symbols referenced by
  -- relocation records; Layout then consumes those planned entries.
  let relocPlan ← Reloc.Result.ofDiscover discovery

  IO.eprintln "\n== 3. Reloc (resolve symbols referenced by dynamic relocations) =="
  let providerName (r : Reloc.Symbol.SymRef relocPlan.graph.objects.size) : String :=
    relocPlan.graph.objects[r.objectIdx.val] |>.name
  let mut relocsTotal := 0
  let mut resolvedTotal := 0
  let mut weakTotal := 0
  let mut noSymbolTotal := 0
  for h : i in [:relocPlan.graph.objects.size] do
    let objectIdx : Fin relocPlan.graph.objects.size := ⟨i, h.upper⟩
    let elf := relocPlan.graph.objects[objectIdx].elf
    for h_seg : segI in [:elf.segments.items.size] do
      let segIdx : Fin elf.segments.items.size := ⟨segI, h_seg.upper⟩
      let entries ← relocPlan.segment objectIdx segIdx
      for entry in entries do
        relocsTotal := relocsTotal + 1
        match entry.target with
        | .noSymbol => noSymbolTotal := noSymbolTotal + 1
        | .weakUnresolved => weakTotal := weakTotal + 1
        | .resolved ref =>
            resolvedTotal := resolvedTotal + 1
            IO.eprintln s!"  [{i}:{segI}] sym[{ref.symIdx}] → {providerName ref}"
  IO.eprintln s!"relocs: {relocsTotal}, resolved: {resolvedTotal}, \
    weak unresolved: {weakTotal}, no-symbol: {noSymbolTotal}"

  let layout ← Layout.Layout.ofRelocResult relocPlan

  IO.eprintln "\n== 4. Layout (kernel-picked reservation + per-object bases) =="
  let lp := layout
  let rsvW ← Runtime.Memory.io.reserve lp.totalSpan
  let bp : Finalize.BoundPlan :=
    { relocPlan with layout := lp, rsv := rsvW.val, h_total := rsvW.property }
  IO.eprintln s!"  reservation = [0x{Nat.hex bp.rsv.addr.toNat}, +0x{Nat.hex lp.totalSpan.toNat})"
  let bases := bp.bases
  for h : i in [:bp.objCount] do
    let base := bases[i]'h.upper
    let obj := relocPlan.graph.objects[i]
    IO.eprintln s!"[{i}] {obj.name} (base=0x{Nat.hex base.toNat}, {obj.elf.segments.items.size} segments)"
    let ep := lp.elfs[i]'h.upper
    for sp in ep.segments do
      let absVa := base + sp.pageEaddr
      IO.eprintln s!"  eaddr=0x{Nat.hex absVa.toNat} len=0x{Nat.hex sp.pageLength.toNat} prot={sp.prot}"
  IO.eprintln s!"init order: {relocPlan.initOrder.order.map (·.val)}"
  IO.eprintln s!"fini order: {(relocPlan.initOrder.order.map (·.val)).reverse}"

  IO.eprintln "\n== 5. Reloc (planned 4/8-byte stores, per-arch formula) =="
  let formula := relocPlan.formula
  let elfs := relocPlan.objectElfs
  let labelW := 16
  for h : i in [:bp.objCount] do
    let obj  := relocPlan.graph.objects[i]
    let base := bases[i]'h.upper
    let label := padR s!"[{i}] {obj.name}" labelW
    let ep := lp.elfs[i]'h.upper
    for h2 : segI in [:ep.segments.size] do
      let sp := ep.segments[segI]
      for entry in sp.relocs do
        let symRef := entry.target.symRef?
        let symValue : UInt64 := match symRef with
          | none => 0
          | some ref =>
            let provBase := bases[ref.objectIdx.val]'ref.objectIdx.isLt
            match elfs[ref.objectIdx]?.bind (·.symtab[ref.symIdx]?) with
            | none     => 0
            | some sym => provBase + sym.value
        let inputs : Reloc.ABI.FormulaInputs :=
          { symValue, addend := entry.addend, base, place := base + (entry.r_offset.val) }
        match formula entry.type inputs with
        | none     => pure ()
        | some res =>
          let symName : String := match entry.target with
            | .noSymbol       => ""
            | .weakUnresolved => "<weak>"
            | .resolved ref   =>
              (elfs[ref.objectIdx]?.bind (·.symtab[ref.symIdx]?)
                |>.bind (·.name)).getD "?"
          let typeStr := padR (toString entry.type) 2
          let sizeBytes : Nat := match res.size with | .b8 => 8 | .b4 => 4
          IO.eprintln s!"{label}  type={typeStr}  seg={segI}  @0x{Nat.hex12 (base + (entry.r_offset.val)).toNat} ← 0x{Nat.hex12 res.value.toNat} ({sizeBytes}B)  sym='{symName}'"
  let lo ← Finalize.build bp
  IO.eprintln s!"planned {lo.mmaps.size} mmaps, \
    {lo.zeros.size} zeros, \
    {lo.stores.size} stores, \
    {lo.mprotects.size} mprotects across {lo.elfs.size} elfs"

  IO.eprintln "\n== 6. Init (DFS post-order over dep DAG) =="
  let ctorAddrs := Finalize.ctorAddrs bp
  let dtorAddrs := Finalize.dtorAddrs bp
  IO.eprintln s!"planned {ctorAddrs.size} constructor address(es), \
    {dtorAddrs.size} destructor address(es)"

  IO.eprintln "\n== 7. Runtime.Run → callCtors → execAndJump (does not return) =="
  realize bp lo ctorAddrs path

private def runCli (action : CliM Unit) : IO UInt32 := do
  IO.ofExcept (← action.run)
  return 0

end Main

/-- LeanLoad CLI. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--debug", path] =>
    Main.runCli (Main.debug path)
  | [path] =>
    Main.runCli (Main.load path)
  | _ =>
    IO.eprintln "usage: leanload [--debug] <path-to-elf>"
    return 1

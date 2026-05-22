/-
LeanLoad CLI + IO orchestration.

`main` is the binary entry point; everything else in this file is
glue that ties the pure core (`Parse` + `Plan`) and the materialize
stage (`Materialize`) to the IO layer (`Runtime`, `Discover.IO`).

The IO bookend `realize` (below) is a thin wrapper:
`Materialize.safe` runs the decidable safety check over the
structured `LoadOps` tree, `LoadOps.runSafe` dispatches to externs,
then the one-shot finalizers (`mmapAnon` for the stack +
`execAndJump`) transfer control. Doesn't return.
-/

import LeanLoad

namespace Main

open LeanLoad

/-- Stack size for the loaded program. Matches musl's default (8 MiB). -/
private def stackBytes : UInt64 := 8 * 1024 * 1024

/-- Run all planned slots inside the kernel-picked reservation,
    allocate the kernel-style stack, and `execAndJump` to entry.
    **Does not return.** -/
private def realize (bp : Materialize.BoundPlan)
    (witnessed : { lo : Materialize.LoadOps bp.objCount //
      Materialize.LoadSafe bp.rsv.addr bp.rsv.len lo })
    (ctorAddrs : Array UInt64) (path : String) : IO Unit := do
  let mainElf := bp.graph.main.elf
  let mainBase := bp.mainBase
  let phdrNbytes : Nat := Parse.RawPhdrSize * mainElf.header.e_phnum.toNat
  let phdrMap ← IO.ofExcept <|
    Parse.PhdrMap.ofSegments mainElf.segments mainElf.header.e_phoff phdrNbytes
  let entry  := mainBase + mainElf.header.e_entry.val
  let phdrVa := mainBase + phdrMap.vaddr.val
  Materialize.LoadOps.runSafe bp.rsv.addr bp.rsv.len witnessed
  -- Ctors run after the address space is fully realized — they're
  -- user code, not kernel ops.
  ctorAddrs.forM Runtime.callCtor
  let stack ← Reserve.run stackBytes
  let phnum  := mainElf.header.e_phnum.toUInt64
  let phent  := Parse.RawPhdrSize.toUInt64
  Runtime.execAndJump entry phdrVa phent phnum 0 stack.val.addr stack.val.len path

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

/-- Discover (IO) → pure-pipeline `Plan` aggregate (resolve + layout
    + relocs + init order) → kernel-picked reservation → Materialize
    → realize. **Does not return.** -/
def load (path : String) : IO Unit := do
  let g ← Discover.discover path
  let plan ← IO.ofExcept (Plan.Aggregate.ofGraph g)
  let rsvW ← Reserve.run plan.layout.totalSpan
  let bp : Materialize.BoundPlan :=
    { plan with rsv := rsvW.val, h_total := rsvW.property }
  let witnessed ← IO.ofExcept (Materialize.build bp)
  let ctorAddrs := Materialize.ctorAddrs bp
  realize bp witnessed ctorAddrs path

/-- `--debug`: same as `load` but with a stage-by-stage summary on
    stderr. Like `load`, this transfers control and does not return. -/
def debug (path : String) : IO Unit := do
  IO.eprintln "== 1. Discover (BFS over DT_NEEDED) =="
  let g ← Discover.discover path
  for obj in g.objects do
    IO.eprintln s!"  {obj.name}"

  IO.eprintln "\n== 2. Parse (per-object checked Elf views) =="
  for h : i in [:g.objects.size] do
    let obj := g.objects[i]
    let elf := obj.elf
    IO.eprintln s!"[{i}] {obj.name}"
    IO.eprintln s!"  elfType    = {repr elf.header.e_type}"
    IO.eprintln s!"  machine    = {repr elf.header.e_machine}"
    IO.eprintln s!"  entry      = 0x{Nat.hex elf.header.e_entry.toNat}"
    IO.eprintln s!"  phnum      = {elf.header.e_phnum}"
    if let some sn := elf.soname  then IO.eprintln s!"  soname     = {sn}"
    if let some rp := elf.runpath then IO.eprintln s!"  runpath    = {rp}"
    if !elf.needed.isEmpty then
      IO.eprintln s!"  needed     = {elf.needed}"
    IO.eprintln s!"  symtab     = {elf.symtab.size} entries"
    IO.eprintln s!"  initArr    = {elf.initArr.size} ctor(s)"
    IO.eprintln s!"  finiArr    = {elf.finiArr.size} dtor(s)"
    IO.eprintln s!"  segments   ({elf.segments.items.size}):"
    for h2 : segI in [:elf.segments.items.size] do
      let seg := elf.segments.items[segI]
      let prot := reprStr seg.perm
      IO.eprintln s!"    [{segI}] vaddr=0x{Nat.hex12 seg.vaddr.toNat} \
        offset=0x{Nat.hex seg.offset.toNat} \
        filesz=0x{Nat.hex seg.filesz.toNat} \
        memsz=0x{Nat.hex seg.memsz.toNat} \
        prot={prot}  rela={seg.rela.size}  jmprel={seg.jmprel.size}"

  -- One-shot pure-pipeline build. Every later stage reads from `plan`.
  let plan ← IO.ofExcept (Plan.Aggregate.ofGraph g)

  IO.eprintln "\n== 3. Resolve (BFS symbol resolution across all elfs) =="
  let providerName (r : Plan.Resolve.SymRef plan.graph.objects.size) : String :=
    plan.graph.objects[r.objectIdx.val] |>.name
  let nameW := plan.resolve.entries.foldl (init := 0) (fun w (u, _) => max w u.name.length)
  let providerW := plan.resolve.entries.foldl (init := "<unresolved>".length) fun w (_, res) =>
    match res with
    | .found r => max w (providerName r).length
    | _        => w
  let mut currentObj : Option Nat := none
  for (u, res) in plan.resolve.entries do
    if currentObj != some u.objectIdx then
      if let some obj := plan.graph.objects[u.objectIdx]? then
        IO.eprintln s!"{obj.name}:"
      currentObj := some u.objectIdx
    let suffix : String := match res with
      | .weakUndef   => s!"{padR "<unresolved>" providerW}  (weak)"
      | .strongUndef => s!"{padR "<unresolved>" providerW}"
      | .found r =>
        let p := padR (providerName r) providerW
        match plan.graph.objects[r.objectIdx]?.bind
            (fun obj => obj.elf.symtab[r.symIdx]?) with
        | some entry => s!"{p} [sym {r.symIdx} @0x{Nat.hex entry.value.toNat}]"
        | none       => s!"{p} [sym {r.symIdx}]"
    IO.eprintln s!"  {padR u.name nameW}  ←  {suffix}"
  IO.eprintln s!"strong missing: {plan.resolve.missing.size}, \
    weak missing: {plan.resolve.weakMissing.size}"

  IO.eprintln "\n== 4. Layout (kernel-picked reservation + per-object bases) =="
  let lp := plan.layout
  let rsvW ← Reserve.run lp.totalSpan
  let bp : Materialize.BoundPlan :=
    { plan with rsv := rsvW.val, h_total := rsvW.property }
  IO.eprintln s!"  reservation = [0x{Nat.hex bp.rsv.addr.toNat}, +0x{Nat.hex lp.totalSpan.toNat})"
  let bases := bp.bases
  for h : i in [:bp.objCount] do
    let base := bases[i]'h.upper
    let obj := plan.graph.objects[i]
    IO.eprintln s!"[{i}] {obj.name} (base=0x{Nat.hex base.toNat}, {obj.elf.segments.items.size} segments)"
    let ep := lp.elfs[i]'h.upper
    for sp in ep.segments do
      let absVa := base + sp.pageVaddr
      IO.eprintln s!"  vaddr=0x{Nat.hex absVa.toNat} len=0x{Nat.hex sp.pageLength.toNat} prot={sp.prot}"
  IO.eprintln s!"init order: {plan.initOrder.map (·.val)}"
  IO.eprintln s!"fini order: {(plan.initOrder.map (·.val)).reverse}"

  IO.eprintln "\n== 5. Reloc (planned 4/8-byte stores, per-arch formula) =="
  let formula := plan.formula
  let elfs := plan.objectElfs
  let labelW := 16
  for h : i in [:bp.objCount] do
    let obj  := plan.graph.objects[i]
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
        let inputs : ABI.FormulaInputs :=
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
  let witnessed ← IO.ofExcept (Materialize.build bp)
  let lo := witnessed.val
  IO.eprintln s!"planned {lo.mmaps.size} mmaps, \
    {lo.zeros.size} zeros, \
    {lo.stores.size} stores, \
    {lo.mprotects.size} mprotects across {lo.size} elfs"

  IO.eprintln "\n== 6. Init (DFS post-order over dep DAG) =="
  let ctorAddrs := Materialize.ctorAddrs bp
  let dtorAddrs := Materialize.dtorAddrs bp
  IO.eprintln s!"planned {ctorAddrs.size} constructor address(es), \
    {dtorAddrs.size} destructor address(es)"

  IO.eprintln "\n== 7. LoadOps.runSafe → callCtors → execAndJump (does not return) =="
  realize bp witnessed ctorAddrs path

end Main

/-- LeanLoad CLI. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--debug", path] =>
    Main.debug path
    return 0
  | [path] =>
    Main.load path
    return 0
  | _ =>
    IO.eprintln "usage: leanload [--debug] <path-to-elf>"
    return 1

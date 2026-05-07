/-
LeanLoad CLI + IO orchestration.

`main` is the binary entry point; everything else in this file is the
glue that ties the verified core (`Spec`, `Parse`, plus the pure
top-level `*Plan` modules) to the FFI layer (`Runtime`). The pipeline
shape (Discover → Resolve → Layout → Map → Reloc → Apply → Init → Exec,
each stage split into pure planner + trusted IO applier) is documented
in the project README.
-/

import LeanLoad

namespace LeanLoad.Main

open LeanLoad

/-- Right-pad a string to `n` chars with `c`. -/
private def padR (s : String) (n : Nat) (c : Char := ' ') : String :=
  s ++ String.ofList (List.replicate (n - s.length) c)

/-- Left-pad a string to `n` chars with `c`. -/
private def padL (s : String) (n : Nat) (c : Char := ' ') : String :=
  String.ofList (List.replicate (n - s.length) c) ++ s

/-- Lower-case hex string of a `Nat`, no `0x` prefix. -/
private def Nat.hex (n : Nat) : String :=
  String.ofList (Nat.toDigits 16 n)

/-- Lower-case hex, zero-padded to 12 digits (covers x86-64
    user-space addresses, which fit in 48 bits / 12 nibbles). -/
private def Nat.hex12 (n : Nat) : String :=
  padL (Nat.hex n) 12 '0'

#guard Nat.hex 0 = "0"
#guard Nat.hex 0x4000b0 = "4000b0"
#guard Nat.hex 0xdeadbeef = "deadbeef"
#guard Nat.hex12 0 = "000000000000"
#guard Nat.hex12 0x7ffffec55d68 = "7ffffec55d68"
#guard padR "abc" 6 '.' = "abc..."
#guard padL "abc" 6 '.' = "...abc"

/-- Discover (IO) → pure planning (Layout, Reloc, Init) →
    Exec.realize (single IO bookend that mmaps, applies patches,
    runs ctors, and jumps). **Does not return** — the loaded program
    terminates the process. -/
def load (path : String) : IO Unit := do
  let rt := Runtime.Ops.real
  let g ← Discover.discover rt path
  let mainObj := g.main
  let resTable := Resolve.buildTable g
  if let some u := resTable.missing[0]? then
    throw (IO.userError s!"load: {resTable.missing.size} unresolved strong symbol(s); first: {u.name}")
  let layouts ← IO.ofExcept g.layouts
  let formula := Elaborate.formulaFor mainObj.elf.machine
  let patches := Reloc.plan formula g layouts.val resTable
  let ctorAddrs := Init.plan g layouts.val (Init.order g)
  -- `layouts`'s subtype carries the per-layout `segmentsSorted`
  -- witness — required by `realize` as a documented precondition
  -- (no `MAP_FIXED` collisions; see `Thm/Layout.layouts_segmentsPairwiseDisjoint`).
  Exec.realize rt g mainObj layouts patches ctorAddrs path

/-- `--debug`: same as `load` but with a header and summary per stage,
    so a developer can see which stages succeeded if the loaded image
    misbehaves. Stage prints go to **stderr** so they don't intermix
    with the loaded program's stdout (and stderr is unbuffered, so we
    don't lose late banners across the `transferControl` fork).
    Like `load`, this transfers control and does not return. -/
def debug (path : String) : IO Unit := do
  let rt := Runtime.Ops.real
  IO.eprintln "== Discover =="
  let g ← Discover.discover rt path
  for obj in g.val do
    IO.eprintln s!"{obj.name}  ({obj.path})"
  let mainObj := g.main

  IO.eprintln "\n== Parse =="
  for h : i in [:g.val.size] do
    let obj := g.val[i]
    let elf := obj.elf
    IO.eprintln s!"[{i}] {obj.name}"
    IO.eprintln s!"  elfType    = {repr elf.elfType}"
    IO.eprintln s!"  machine    = {repr elf.machine}"
    IO.eprintln s!"  entry      = 0x{Nat.hex elf.entry.toNat}"
    IO.eprintln s!"  phnum      = {elf.phnum}"
    if let some sn := elf.soname  then IO.eprintln s!"  soname     = {sn}"
    if let some rp := elf.runpath then IO.eprintln s!"  runpath    = {rp}"
    if !elf.needed.isEmpty then
      IO.eprintln s!"  needed     = {elf.needed}"
    IO.eprintln s!"  symtab     = {elf.symtab.size} entries"
    IO.eprintln s!"  initArr    = {elf.initArr.size} ctor(s)"
    IO.eprintln s!"  segments   ({elf.segments.size}):"
    for h2 : segI in [:elf.segments.size] do
      let seg := elf.segments[segI]
      let prot := toString seg.perm
      IO.eprintln s!"    [{segI}] vaddr=0x{Nat.hex12 seg.vaddr.toNat} \
        offset=0x{Nat.hex seg.offset.toNat} \
        filesz=0x{Nat.hex seg.filesz.toNat} \
        memsz=0x{Nat.hex seg.memsz.toNat} \
        prot={prot}  rela={seg.rela.size}  jmprel={seg.jmprel.size}"

  IO.eprintln "\n== Resolve =="
  let resTable := Resolve.buildTable g
  let providerName (r : Resolve.SymRef g.val.size) : String := g.val[r.objectIdx].name
  let nameW := resTable.resolved.foldl (init := 0) (fun w (u, _) => max w u.name.length)
  let providerW := resTable.resolved.foldl (init := "<unresolved>".length) fun w (_, ref?) =>
    match ref? with
    | none   => w
    | some r => max w (providerName r).length
  let mut currentObj : Option Nat := none
  for (u, ref?) in resTable.resolved do
    if currentObj != some u.objectIdx then
      if let some obj := g.val[u.objectIdx]? then
        IO.eprintln s!"{obj.name}:"
      currentObj := some u.objectIdx
    let suffix : String := match ref? with
      | none =>
        let weakTag :=
          match g.val[u.objectIdx]?.bind (fun obj => obj.elf.symtab[u.symIdx]?) with
          | some entry => if entry.isWeak then "  (weak)" else ""
          | none       => ""
        s!"{padR "<unresolved>" providerW}{weakTag}"
      | some r =>
        let p := padR (providerName r) providerW
        match g.val[r.objectIdx]?.bind (fun obj => obj.elf.symtab[r.symIdx]?) with
        | some entry => s!"{p} [sym {r.symIdx} @0x{Nat.hex entry.value.toNat}]"
        | none       => s!"{p} [sym {r.symIdx}]"
    IO.eprintln s!"  {padR u.name nameW}  ←  {suffix}"
  IO.eprintln s!"strong missing: {resTable.missing.size}, weak missing: {resTable.weakMissing.size}"

  IO.eprintln "\n== Layout =="
  let layouts ← IO.ofExcept g.layouts
  -- layouts.val.size = g.val.size by construction; iterate by index.
  for h : i in [:g.val.size] do
    let lyt := layouts.val[i]'(layouts.property.left.symm ▸ h.upper)
    let obj := g.val[i]
    IO.eprintln s!"[{i}] {obj.name} ({lyt.segments.size} segments)"
    if let some e := lyt.entry then
      IO.eprintln s!"  entry: 0x{Nat.hex e.toNat}"
    for s in lyt.segments do
      IO.eprintln s!"  vaddr=0x{Nat.hex s.pageVaddr.toNat} len=0x{Nat.hex s.pageLength.toNat} prot={s.prot}"
  let initOrder := Init.order g
  IO.eprintln s!"init order: {initOrder}"
  IO.eprintln s!"fini order: {initOrder.reverse}"

  IO.eprintln "\n== Reloc =="
  let formula := Elaborate.formulaFor mainObj.elf.machine
  let labelW := 16
  let bases := layouts.val.map (·.base)
  -- Re-walk each object's per-segment relas to enrich each patch with
  -- its type and symbol name. `Exec.realize` below uses the same
  -- formula via `Reloc.plan`, so the trace and the patches match.
  for h : i in [:g.val.size] do
    let obj  := g.val[i]
    let some lyt := layouts.val[i]? | continue
    let base := lyt.base
    let label := padR s!"[{i}] {obj.name}" labelW
    let printOne (segI : Nat) (r : Parse.RawRela) : IO Unit := do
      let symValue : UInt64 := if r.sym == 0 then 0
        else Reloc.resolveSymValue g bases resTable i r.sym.toNat
      let inputs : Elaborate.FormulaInputs :=
        { symValue, addend := r.r_addend, base, place := base + r.r_offset }
      match formula r.type inputs with
      | none     => pure ()
      | some res =>
        let symName : String :=
          if r.sym == 0 then ""
          else (obj.elf.symtab[r.sym.toNat]?.bind (·.name)).getD "?"
        let typeStr := padR (toString r.type) 2
        IO.eprintln s!"{label}  type={typeStr}  seg={segI}  @0x{Nat.hex12 (base + r.r_offset).toNat} ← 0x{Nat.hex12 res.value.toNat} ({res.size.toNat}B)  sym='{symName}'"
    for h2 : segI in [:obj.elf.segments.size] do
      let seg := obj.elf.segments[segI]
      for entry in seg.rela do printOne segI entry.val
      for entry in seg.jmprel do printOne segI entry.val
  let patches := Reloc.plan formula g layouts.val resTable
  IO.eprintln s!"planned {patches.size} patches"

  IO.eprintln "\n== InitPlan =="
  let ctorAddrs := Init.plan g layouts.val initOrder
  IO.eprintln s!"planned {ctorAddrs.size} constructor(s)"

  IO.eprintln "\n== Realize =="
  Exec.realize rt g mainObj layouts patches ctorAddrs path

end LeanLoad.Main

/-- LeanLoad CLI.

    `leanload <elf>`          — load and run a binary via kernel-style
                                exec. Static or dynamic. Does not return.
    `leanload --debug <elf>`  — same, with a stage-by-stage summary
                                printed before transfer of control.
                                Useful for isolating which stage
                                misbehaves when the loaded image crashes.
-/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--debug", path] =>
    LeanLoad.Main.debug path
    return 0
  | [path] =>
    LeanLoad.Main.load path
    return 0  -- unreachable; loaded program terminates the process
  | _ =>
    IO.eprintln "usage: leanload [--debug] <path-to-elf>"
    return 1

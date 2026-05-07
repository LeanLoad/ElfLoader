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
  -- realize takes only the size proof; the sortedness witness is
  -- proof-only material that isn't consumed by the IO sweep.
  let sizedLayouts : { a : Array Layout.ObjectLayout // a.size = g.val.size } :=
    ⟨layouts.val, layouts.property.left⟩
  let some formula := Spec.Reloc.formulaFor mainObj.elf.header.e_machine
    | throw (IO.userError s!"load: unsupported e_machine={mainObj.elf.header.e_machine} (need EM_AARCH64=183 or EM_X86_64=62)")
  let patches ← IO.ofExcept (Reloc.plan formula g layouts.val resTable)
  let ctorAddrs := Init.plan g layouts.val (Init.order g)
  Exec.realize rt g mainObj sizedLayouts patches ctorAddrs path

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
          | some sym => if Resolve.isWeak sym then "  (weak)" else ""
          | none     => ""
        s!"{padR "<unresolved>" providerW}{weakTag}"
      | some r =>
        let p := padR (providerName r) providerW
        match g.val[r.objectIdx]?.bind (fun obj => obj.elf.symtab[r.symIdx]?) with
        | some sym => s!"{p} [sym {r.symIdx} @0x{Nat.hex sym.st_value.toNat}]"
        | none     => s!"{p} [sym {r.symIdx}]"
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
      IO.eprintln s!"  vaddr=0x{Nat.hex s.vaddr.toNat} len=0x{Nat.hex s.length.toNat} prot={s.prot}"
  let initOrder := Init.order g
  IO.eprintln s!"init order: {initOrder}"
  IO.eprintln s!"fini order: {initOrder.reverse}"

  IO.eprintln "\n== Reloc =="
  let some formula := Spec.Reloc.formulaFor mainObj.elf.header.e_machine
    | throw (IO.userError s!"debug: unsupported e_machine={mainObj.elf.header.e_machine}")
  let labelW := 16
  let bases := layouts.val.map (·.base)
  -- Re-walk each object's relas to enrich each patch with its type
  -- and symbol name. `Exec.realize` below uses the same formula via
  -- `Reloc.plan`, so the trace and the patches match.
  for h : i in [:g.val.size] do
    let obj  := g.val[i]
    let some lyt := layouts.val[i]? | continue
    let base := lyt.base
    let label := padR s!"[{i}] {obj.name}" labelW
    let printOne (r : Spec.Reloc.Rela64) : IO Unit := do
      let symValue : UInt64 := if r.sym == 0 then 0
        else Reloc.resolveSymValue g bases resTable i r.sym.toNat
      let inputs : Spec.Reloc.FormulaInputs :=
        { symValue, addend := r.r_addend, base, place := base + r.r_offset }
      match formula r.type inputs with
      | none     => pure ()
      | some res =>
        let symName : String :=
          if r.sym == 0 then ""
          else (obj.elf.symtab[r.sym.toNat]?.bind fun s =>
                  Spec.StringTable.lookup obj.elf.strtab s.st_name.toNat).getD "?"
        let typeStr := padR (toString r.type) 2
        IO.eprintln s!"{label}  type={typeStr}  @0x{Nat.hex12 (base + r.r_offset).toNat} ← 0x{Nat.hex12 res.value.toNat} ({res.size.toNat}B)  sym='{symName}'"
    for r in obj.elf.rela do printOne r
    for r in obj.elf.jmprel do printOne r
  let patches ← IO.ofExcept (Reloc.plan formula g layouts.val resTable)
  IO.eprintln s!"planned {patches.size} patches"

  IO.eprintln "\n== InitPlan =="
  let ctorAddrs := Init.plan g layouts.val initOrder
  IO.eprintln s!"planned {ctorAddrs.size} constructor(s)"

  IO.eprintln "\n== Realize =="
  let sizedLayouts : { a : Array Layout.ObjectLayout // a.size = g.val.size } :=
    ⟨layouts.val, layouts.property.left⟩
  Exec.realize rt g mainObj sizedLayouts patches ctorAddrs path

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

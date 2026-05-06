/-
LeanLoad CLI + IO orchestration.

`main` is the binary entry point; everything else in this file is the
glue that ties the verified core (`Spec`, `Parse`, plus the pure
top-level modules `Resolve`, `Layout`, `Reloc`, `Spec/Reloc/Formula`)
to the FFI layer (`runtime/`). Verified code must not import
`LeanLoad.Region`'s externs; everything that crosses into the kernel
goes through this file (`Main.lean`), `Map.lean`, `Apply.lean`, or
`Exec.lean`.

Pipeline:
  1. Discover (IO):   path → dep graph
  2. Resolve  (pure): dep graph → resolution table
  3. Layout   (pure): dep graph → per-object layouts (`g.layouts`)
  4. Order    (pure): dep graph → init order (`g.order`)
  5. Map      (IO):   layouts → regions at chosen bases
  6. Reloc    (pure): dep graph × layouts × resolution → patches
  7. Apply    (IO):   patches → memory mutated
  8. Init     (IO):   image × order → constructors called
  9. Exec     (IO):   no return
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

/-- Discover + layout + map + relocate + run inits + jump.
    **Does not return** — the loaded program terminates the process. -/
def load (path : String) : IO Unit := do
  let g ← Discover.discover path
  let some mainObj := g.objects[0]?
    | throw (IO.userError "load: empty dep graph")
  let rt   := Resolve.buildTable g
  if let some u := rt.missing[0]? then
    throw (IO.userError s!"load: {rt.missing.size} unresolved strong symbol(s); first: {u.name}")
  let layouts ← IO.ofExcept g.layouts
  let image ← Map.mapAll g layouts
  let some formula := Spec.Reloc.formulaFor mainObj.elf.header.e_machine
    | throw (IO.userError s!"load: unsupported e_machine={mainObj.elf.header.e_machine} (need EM_AARCH64=183 or EM_X86_64=62)")
  let patches ← IO.ofExcept (Reloc.plan formula g layouts rt)
  Apply.applyPatches image patches
  Exec.runInits g image g.order
  Exec.transferControl mainObj image path

/-- `--debug`: same as `load` but with a header and summary per stage,
    so a developer can see which stages succeeded if the loaded image
    misbehaves. Stage prints go to **stderr** so they don't intermix
    with the loaded program's stdout (and stderr is unbuffered, so we
    don't lose late banners across the `transferControl` fork).
    Like `load`, this transfers control and does not return. -/
def debug (path : String) : IO Unit := do
  IO.eprintln "== Discover =="
  let g ← Discover.discover path
  for obj in g.objects do
    IO.eprintln s!"{obj.name}  ({obj.path})"
  let some mainObj := g.objects[0]?
    | throw (IO.userError "debug: empty dep graph")

  IO.eprintln "\n== Resolve =="
  let rt := Resolve.buildTable g
  let providerName (r : Resolve.SymRef) : String := match g.objects[r.objectIdx]? with
    | some obj => obj.name
    | none     => "?"
  let nameW := rt.resolved.foldl (init := 0) (fun w (u, _) => max w u.name.length)
  let providerW := rt.resolved.foldl (init := "<unresolved>".length) fun w (_, ref?) =>
    match ref? with
    | none   => w
    | some r => max w (providerName r).length
  let mut currentObj : Option Nat := none
  for (u, ref?) in rt.resolved do
    if currentObj != some u.objectIdx then
      if let some obj := g.objects[u.objectIdx]? then
        IO.eprintln s!"{obj.name}:"
      currentObj := some u.objectIdx
    let suffix : String := match ref? with
      | none =>
        let weakTag :=
          match g.objects[u.objectIdx]?.bind (fun obj => obj.elf.symtab[u.symIdx]?) with
          | some sym => if Resolve.isWeak sym then "  (weak)" else ""
          | none     => ""
        s!"{padR "<unresolved>" providerW}{weakTag}"
      | some r =>
        let p := padR (providerName r) providerW
        match g.objects[r.objectIdx]?.bind (fun obj => obj.elf.symtab[r.symIdx]?) with
        | some sym => s!"{p} [sym {r.symIdx} @0x{Nat.hex sym.st_value.toNat}]"
        | none     => s!"{p} [sym {r.symIdx}]"
    IO.eprintln s!"  {padR u.name nameW}  ←  {suffix}"
  IO.eprintln s!"strong missing: {rt.missing.size}, weak missing: {rt.weakMissing.size}"

  IO.eprintln "\n== Layout =="
  let layouts ← IO.ofExcept g.layouts
  -- layouts.val.size = g.objects.size by construction; iterate by index.
  for h : i in [:g.objects.size] do
    let lyt := layouts.val[i]'(layouts.property.symm ▸ h.upper)
    let obj := g.objects[i]
    IO.eprintln s!"[{i}] {obj.name} ({lyt.segments.size} segments)"
    if let some e := lyt.entry then
      IO.eprintln s!"  entry: 0x{Nat.hex e.toNat}"
    for s in lyt.segments do
      IO.eprintln s!"  vaddr=0x{Nat.hex s.vaddr.toNat} len=0x{Nat.hex s.length.toNat} prot={s.prot}"
  IO.eprintln s!"init order: {g.order}"
  IO.eprintln s!"fini order: {g.order.reverse}"

  IO.eprintln "\n== Map =="
  let image ← Map.mapAll g layouts
  for i in [:image.objects.size] do
    let some obj    := g.objects[i]?     | continue
    let some imgObj := image.objects[i]? | continue
    IO.eprintln s!"[{i}] {obj.name} → 0x{Nat.hex imgObj.layout.base.toNat}"

  IO.eprintln "\n== Reloc =="
  let some formula := Spec.Reloc.formulaFor mainObj.elf.header.e_machine
    | throw (IO.userError s!"debug: unsupported e_machine={mainObj.elf.header.e_machine}")
  let labelW := 16
  let bases := image.objects.map (·.layout.base)
  -- Re-walk each object's relas to enrich each patch with its type
  -- and symbol name. The actual `applyPatches` below uses the same
  -- formula via `Reloc.plan`, so the trace and the patches match.
  for i in [:g.objects.size] do
    let some obj    := g.objects[i]? | continue
    let some imgObj := image.objects[i]? | continue
    let base := imgObj.layout.base
    let label := padR s!"[{i}] {obj.name}" labelW
    let printOne (r : Spec.Reloc.Rela64) : IO Unit := do
      let symValue : UInt64 := if r.sym == 0 then 0
        else Reloc.resolveSymValue g bases rt i r.sym.toNat
      let inputs : Reloc.FormulaInputs :=
        { symValue, addend := r.r_addend, base, place := base + r.r_offset }
      match formula r.type inputs with
      | none     => pure ()
      | some res =>
        let symName : String :=
          if r.sym == 0 then ""
          else (obj.elf.symtab[r.sym.toNat]?.bind fun s =>
                  Spec.StringTable.lookup obj.elf.strtab s.st_name.toNat).getD "?"
        let typeStr := padR (toString r.type) 2
        IO.eprintln s!"{label}  type={typeStr}  @0x{Nat.hex12 (base + r.r_offset).toNat} ← 0x{Nat.hex12 res.value.toNat} ({res.size}B)  sym='{symName}'"
    for r in obj.elf.rela do printOne r
    for r in obj.elf.jmprel do printOne r
  let patches ← IO.ofExcept (Reloc.plan formula g layouts rt)
  IO.eprintln s!"planned {patches.size} patches"

  IO.eprintln "\n== Apply =="
  Apply.applyPatches image patches
  IO.eprintln s!"applied {patches.size} patches"

  IO.eprintln "\n== Init =="
  Exec.runInits g image g.order
  IO.eprintln "done"

  IO.eprintln "\n== Exec =="
  Exec.transferControl mainObj image path

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

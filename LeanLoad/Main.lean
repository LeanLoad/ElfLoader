/-
LeanLoad CLI + IO orchestration.

`main` is the binary entry point; everything else in this file is the
glue that ties the verified core (`Spec`, `Parse`, `Plan`) to the FFI
layer (`runtime/`). Verified code (`Spec/`, `Parse/`, plus the pure
modules `Resolve.lean`, `Layout.lean`, `Reloc.lean`,
`Spec/Reloc/Formula.lean`) must not import `LeanLoad.Region`'s
externs; everything that crosses into the kernel goes through this
file (`Main.lean`), `Map.lean`, `Apply.lean`, or `Exec.lean`.

Pipeline:
  1. Discover (IO):  path → link map
  2. Resolve (pure): link map → resolution table
  3. Plan    (pure): link map → layouts + init order  (no bases)
  4. Map     (IO):   layouts → regions × kernel-chosen bases
  5. Reloc   (pure): link map × resolution × bases → writes
  6. Apply   (IO):   writes → memory mutated
  7. Init    (IO):   bases × init order → constructors called
  8. Exec    (IO):   no return
-/

import LeanLoad

namespace LeanLoad.Load

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

/-- Discover + plan + map + relocate + run inits + jump.
    **Does not return** — the loaded program terminates the process. -/
def load (path : String) : IO Unit := do
  let lm ← Discover.discover path
  let some mainObj := lm.objects[0]?
    | throw (IO.userError "load: empty link map")
  let rt   := Resolve.buildTable lm
  let plan := Layout.fromLinkMap lm (Layout.initOrder lm) (Layout.finiOrder lm)
  let (allRegions, bases) ← mapAll lm plan
  let some formula := Spec.Reloc.formulaFor mainObj.elf.header.e_machine
    | throw (IO.userError s!"load: unsupported e_machine={mainObj.elf.header.e_machine} (need EM_AARCH64=183 or EM_X86_64=62)")
  let writes := Reloc.plan formula lm bases rt
  applyAllRelocs allRegions bases writes
  runInits lm bases plan
  transferControl mainObj plan bases path

/-- `--debug`: same as `load` but with a header and summary per stage,
    so a developer can see which stages succeeded if the loaded image
    misbehaves. Like `load`, this transfers control and does not
    return — the loaded program owns the process. -/
def debug (path : String) : IO Unit := do
  IO.println "== Discover =="
  let lm ← Discover.discover path
  for obj in lm.objects do
    IO.println s!"{obj.name}  ({obj.path})"
  let some mainObj := lm.objects[0]?
    | throw (IO.userError "debug: empty link map")

  IO.println "\n== Resolve =="
  let rt := Resolve.buildTable lm
  let providerName (r : Resolve.SymRef) : String := match lm.objects[r.objectIdx]? with
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
      if let some obj := lm.objects[u.objectIdx]? then
        IO.println s!"{obj.name}:"
      currentObj := some u.objectIdx
    let suffix : String := match ref? with
      | none =>
        let weakTag :=
          match lm.objects[u.objectIdx]?.bind (fun obj => obj.elf.symtab[u.symIdx]?) with
          | some sym => if Resolve.isWeak sym then "  (weak)" else ""
          | none     => ""
        s!"{padR "<unresolved>" providerW}{weakTag}"
      | some r =>
        let p := padR (providerName r) providerW
        match lm.objects[r.objectIdx]?.bind (fun obj => obj.elf.symtab[r.symIdx]?) with
        | some sym => s!"{p} [sym {r.symIdx} @0x{Nat.hex sym.st_value.toNat}]"
        | none     => s!"{p} [sym {r.symIdx}]"
    IO.println s!"  {padR u.name nameW}  ←  {suffix}"
  IO.println s!"strong missing: {rt.missing.size}, weak missing: {rt.weakMissing.size}"

  IO.println "\n== Plan =="
  let plan := Layout.fromLinkMap lm (Layout.initOrder lm) (Layout.finiOrder lm)
  for lyt in plan.layouts do
    let some obj := lm.objects[lyt.objectIdx]? | continue
    IO.println s!"[{lyt.objectIdx}] {obj.name} ({lyt.mappings.size} mappings)"
    if let some e := lyt.entry then
      IO.println s!"  entry: 0x{Nat.hex e.toNat}"
    for m in lyt.mappings do
      IO.println s!"  vaddr=0x{Nat.hex m.vaddr.toNat} len=0x{Nat.hex m.length.toNat} prot={m.prot}"
  IO.println s!"init order: {plan.initOrder}"
  IO.println s!"fini order: {plan.finiOrder}"

  IO.println "\n== Map =="
  let (allRegions, bases) ← mapAll lm plan
  for i in [:bases.size] do
    let some obj := lm.objects[i]? | continue
    let some b := bases[i]? | continue
    IO.println s!"[{i}] {obj.name} → 0x{Nat.hex b.toNat}"

  IO.println "\n== Reloc =="
  let some formula := Spec.Reloc.formulaFor mainObj.elf.header.e_machine
    | throw (IO.userError s!"debug: unsupported e_machine={mainObj.elf.header.e_machine}")
  -- Width of the "[i] objname" prefix. Fixed; column will be ragged
  -- if a fixture has unusually long names.
  let labelW := 16
  -- Re-walk each object's relas to enrich each write with its type
  -- and symbol name. The actual `applyAllRelocs` below uses the same
  -- formula via `Reloc.plan`, so the trace and the writes match.
  for i in [:lm.objects.size] do
    let some obj := lm.objects[i]? | continue
    let some base := bases[i]? | continue
    let label := padR s!"[{i}] {obj.name}" labelW
    let printOne (r : Spec.Reloc.Rela64) : IO Unit := do
      let symValue : UInt64 := if r.sym == 0 then 0
        else Reloc.resolveSymValue lm bases rt obj base i r.sym.toNat
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
        IO.println s!"{label}  type={typeStr}  @0x{Nat.hex12 (base + r.r_offset).toNat} ← 0x{Nat.hex12 res.value.toNat} ({res.size}B)  sym='{symName}'"
    for r in obj.elf.rela do printOne r
    for r in obj.elf.jmprel do printOne r
  let writes := Reloc.plan formula lm bases rt
  IO.println s!"planned {writes.size} writes"

  IO.println "\n== Apply =="
  applyAllRelocs allRegions bases writes
  IO.println s!"applied {writes.size} writes"

  IO.println "\n== Init =="
  runInits lm bases plan
  IO.println "done"

  IO.println "\n== Exec =="
  transferControl mainObj plan bases path

end LeanLoad.Load

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
    LeanLoad.Load.debug path
    return 0
  | [path] =>
    LeanLoad.Load.load path
    return 0  -- unreachable; loaded program terminates the process
  | _ =>
    IO.eprintln "usage: leanload [--debug] <path-to-elf>"
    return 1

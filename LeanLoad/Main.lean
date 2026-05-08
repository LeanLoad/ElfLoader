/-
LeanLoad CLI + IO orchestration.

`main` is the binary entry point; everything else in this file is
glue that ties the pure core (`Parse` + `Elaborate` + `Plan`) and
the materialize stage (`Materialize`) to the IO layer
(`Runtime`, `Discover.IO`).

The IO bookend `realize` (below) is a thin wrapper:
`Materialize.safe` runs the decidable safety check over the
structured `LoadOps` tree, `LoadOps.runSafe` dispatches to externs,
then the one-shot finalizers (`mmapAnon` for the stack +
`execAndJump`) transfer control. Doesn't return.
-/

import LeanLoad

namespace LeanLoad.Main

open LeanLoad
open LeanLoad.Elaborate (Elf)

/-- Stack size for the loaded program. Matches musl's default (8 MiB). -/
private def stackBytes : UInt64 := 8 * 1024 * 1024

/-- Run all planned slots inside the kernel-picked reservation,
    allocate the kernel-style stack, and `execAndJump` to entry.
    **Does not return.** -/
private def realize (rsvAddr rsvLen : UInt64)
    (lo : Materialize.LoadOps) (mainElf : Elf)
    (ctorAddrs : Array UInt64) (path : String) : IO Unit := do
  let witnessed ← IO.ofExcept (Materialize.safe rsvAddr rsvLen lo)
  Materialize.LoadOps.runSafe rsvAddr rsvLen witnessed
  -- Ctors run after the address space is fully realized — they're
  -- user code, not kernel ops.
  ctorAddrs.forM Runtime.callCtor
  let mainEo ← match lo[0]? with
    | some eo => pure eo
    | none    => throw (IO.userError "realize: empty load tree")
  let mainBase := mainEo.base
  let stackVa ← Runtime.mmapAnon stackBytes
  let entry  := mainBase + mainElf.entry
  let phdrVa := mainBase + mainElf.phoff
  let phnum  := mainElf.phnum.toUInt64
  let phent  := Parse.RawPhdrSize.toUInt64
  Runtime.execAndJump entry phdrVa phent phnum 0 stackVa stackBytes path

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

/-- Discover (IO) → pure base-free planning (Layout, Resolve, Reloc,
    Init order) → kernel-picked reservation → assignBases →
    Materialize → realize. **Does not return.** -/
def load (path : String) : IO Unit := do
  let g ← Discover.discover path
  let elfs    := g.val.map (·.elf)
  let handles := g.val.map (·.handle)
  have h_size : handles.size = elfs.size := by simp [elfs, handles]
  have _h_pos  : 0 < elfs.size := by simp [elfs]; exact g.property
  let mainElf := g.main.elf
  let resTable := Resolve.buildTable elfs
  if let some u := resTable.missing[0]? then
    throw (IO.userError s!"load: {resTable.missing.size} unresolved strong symbol(s); first: {u.name}")
  -- Pure base-free planning.
  let lpW ← IO.ofExcept (Plan.LoadPlan.ofElfs elfs)
  let lp := lpW.val
  have h_lp : elfs.size = lp.elfs.size := lpW.property.symm
  let relocPlan := Reloc.planAll elfs resTable
  let initOrder := Init.order g
  -- Kernel-picked reservation covering every loaded object.
  let rsvAddr ← Runtime.mmapAnon lp.totalSpan
  let bases := Plan.assignBases rsvAddr lp
  have h_bases : bases.size = elfs.size :=
    (Plan.assignBases_size rsvAddr lp).trans h_lp.symm
  let formula := Elaborate.formulaFor mainElf.machine
  let lo ← IO.ofExcept (Materialize.build lp elfs h_lp handles h_size
    bases h_bases formula relocPlan)
  let ctorAddrs := Materialize.initAddrs lp bases initOrder
  realize rsvAddr lp.totalSpan lo mainElf ctorAddrs path

/-- `--debug`: same as `load` but with a stage-by-stage summary on
    stderr. Like `load`, this transfers control and does not return. -/
def debug (path : String) : IO Unit := do
  IO.eprintln "== 1. Discover (BFS over DT_NEEDED) =="
  let g ← Discover.discover path
  for obj in g.val do
    IO.eprintln s!"  {obj.name}"
  let elfs    := g.val.map (·.elf)
  let handles := g.val.map (·.handle)
  have h_size : handles.size = elfs.size := by simp [elfs, handles]
  have _h_pos  : 0 < elfs.size := by simp [elfs]; exact g.property
  let mainElf := g.main.elf

  IO.eprintln "\n== 2. Parse + Elaborate (per-object Elf views) =="
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

  IO.eprintln "\n== 3. Resolve (BFS symbol resolution across all elfs) =="
  let resTable := Resolve.buildTable elfs
  have h_eq : elfs.size = g.val.size := by simp [elfs]
  let providerName (r : Resolve.SymRef elfs.size) : String :=
    g.val[r.objectIdx.val]'(h_eq ▸ r.objectIdx.isLt) |>.name
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

  IO.eprintln "\n== 4. Layout (kernel-picked reservation + per-object bases) =="
  let lpW ← IO.ofExcept (Plan.LoadPlan.ofElfs elfs)
  let lp := lpW.val
  have h_lp : elfs.size = lp.elfs.size := lpW.property.symm
  let rsvAddr ← Runtime.mmapAnon lp.totalSpan
  IO.eprintln s!"  reservation = [0x{Nat.hex rsvAddr.toNat}, +0x{Nat.hex lp.totalSpan.toNat})"
  let bases := Plan.assignBases rsvAddr lp
  have h_bases : bases.size = elfs.size :=
    (Plan.assignBases_size rsvAddr lp).trans h_lp.symm
  for h : i in [:g.val.size] do
    let base := bases[i]'(by rw [h_bases]; simp [elfs]; exact h.upper)
    let obj := g.val[i]
    IO.eprintln s!"[{i}] {obj.name} (base=0x{Nat.hex base.toNat}, {obj.elf.segments.size} segments)"
    have hi_lp : i < lp.elfs.size := h_lp ▸ (by simp [elfs]; exact h.upper)
    let ep := lp.elfs[i]'hi_lp
    for sp in ep.segments do
      let absVa := base + sp.pageVaddr
      IO.eprintln s!"  vaddr=0x{Nat.hex absVa.toNat} len=0x{Nat.hex sp.pageLength.toNat} prot={sp.prot}"
  let initOrder := Init.order g
  IO.eprintln s!"init order: {initOrder}"
  IO.eprintln s!"fini order: {initOrder.reverse}"

  IO.eprintln "\n== 5. Reloc (planned 4/8-byte stores, per-arch formula) =="
  let formula := Elaborate.formulaFor mainElf.machine
  let relocPlan := Reloc.planAll elfs resTable
  let labelW := 16
  for h : i in [:g.val.size] do
    let obj  := g.val[i]
    let some base := bases[i]? | continue
    let label := padR s!"[{i}] {obj.name}" labelW
    let elfRelocs := (relocPlan[i]?).getD #[]
    for h2 : segI in [:obj.elf.segments.size] do
      let segRelocs := (elfRelocs[segI]?).getD #[]
      for entry in segRelocs do
        let symValue : UInt64 := match entry.target with
          | none => 0
          | some ref =>
            match bases[ref.objectIdx.val]? with
            | none => 0
            | some provBase =>
              match elfs[ref.objectIdx].symtab[ref.symIdx]? with
              | none     => 0
              | some sym => provBase + sym.value
        let inputs : Elaborate.FormulaInputs :=
          { symValue, addend := entry.addend, base, place := base + entry.r_offset }
        match formula entry.type inputs with
        | none     => pure ()
        | some res =>
          let symName : String := match entry.target with
            | none => ""
            | some ref =>
              (elfs[ref.objectIdx].symtab[ref.symIdx]?.bind (·.name)).getD "?"
          let typeStr := padR (toString entry.type) 2
          let sizeBytes : Nat := match res.size with | .b8 => 8 | .b4 => 4
          IO.eprintln s!"{label}  type={typeStr}  seg={segI}  @0x{Nat.hex12 (base + entry.r_offset).toNat} ← 0x{Nat.hex12 res.value.toNat} ({sizeBytes}B)  sym='{symName}'"
  let lo ← IO.ofExcept
    (Materialize.build lp elfs h_lp handles h_size bases h_bases formula relocPlan)
  IO.eprintln s!"planned {lo.mmaps.size} mmaps, \
    {lo.zeros.size} zeros, \
    {lo.stores.size} stores, \
    {lo.mprotects.size} mprotects across {lo.size} elfs"

  IO.eprintln "\n== 6. Init (DFS post-order over dep DAG) =="
  let ctorAddrs := Materialize.initAddrs lp bases initOrder
  IO.eprintln s!"planned {ctorAddrs.size} constructor address(es)"

  IO.eprintln "\n== 7. Materialize.safe → LoadOps.runSafe → callCtors → execAndJump (does not return) =="
  realize rsvAddr lp.totalSpan lo mainElf ctorAddrs path

end LeanLoad.Main

/-- LeanLoad CLI. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--debug", path] =>
    LeanLoad.Main.debug path
    return 0
  | [path] =>
    LeanLoad.Main.load path
    return 0
  | _ =>
    IO.eprintln "usage: leanload [--debug] <path-to-elf>"
    return 1

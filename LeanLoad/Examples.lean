/-
Fixture-driven integration examples.

`LeanLoad.Parse.Examples` owns the literal ELF bytes. This module starts from
that checked parse result and walks the pure pipeline shape production uses:

  * Discover loads the main fixture plus its two DT_NEEDED dependencies.
  * Reloc resolves the fixture's dynamic relocations against that graph.
  * Layout assigns deterministic example bases.
  * Finalize bakes concrete load operations inside a fixed reservation.

The dependency objects deliberately reuse the parsed fixture's PT_LOAD layout so
the example stays anchored to one real byte image, but they clear dynamic edges
and relocations. `libc.so.6` defines the one strong symbol the fixture imports.
-/

import LeanLoad.Parse.Examples
import LeanLoad.Discover.Finalize
import LeanLoad.Reloc
import LeanLoad.Layout.Basic
import LeanLoad.Finalize.Build

namespace LeanLoad.Examples

open LeanLoad.Parse

private def mainPath : String := "/examples/fixture-main"
private def reservationBase : UInt64 := 0x80000000

private def dummyFile : Runtime.File :=
  { backing := .virtual
    size := 0
    read := fun range =>
      throw s!"integration example dummy file cannot read {range.size.toNat} bytes \
        at file offset 0x{range.off.toNat}" }

private def parsedFixture : Except String Elf :=
  Parse.Examples.fixture

private def putsDefinition : Symbol :=
  { name := "puts", bind := .global, shndx := .concrete 1, value := 0x220 }

private def providerElf (soname : String) (symtab : Array Symbol) (template : Elf) :
    Elf :=
  { template with
    symtab := symtab
    needed := #[]
    soname := some soname
    rpath := none
    runpath := none
    relocs := { rela := #[], jmprel := #[] }
    callTargets := CallTargets.empty template.segments }

private def libcElf (template : Elf) : Elf :=
  providerElf "libc.so.6" #[default, putsDefinition] template

private def libmElf (template : Elf) : Elf :=
  providerElf "libm.so.6" #[default] template

private def dependencyObject (name : String) (elf : Elf) : Discover.DiscoveredObject :=
  { name := name, handle := dummyFile, originDir := none, elf := elf }

private def fixtureFinder (main libc libm : Elf) :
    Discover.ObjectFinder (Except String) :=
  { findMain := fun path =>
     .ok (Discover.DiscoveredObject.ofMain path dummyFile none main)
    findDependency := fun work =>
      match work.needed with
      | "libc.so.6" => .ok (some (dependencyObject "libc.so.6" libc))
      | "libm.so.6" => .ok (some (dependencyObject "libm.so.6" libm))
      | _ => .ok none }

private def discovery : Except String Discover.Result := do
  let main ← parsedFixture
  Discover.discover (fixtureFinder main (libcElf main) (libmElf main)) 16 mainPath

private def graph? : Option Discover.LoadGraph :=
  discovery.toOption.map (·.graph)

private def graphNames? : Option (Array String) :=
  graph?.map (fun g => g.objects.map (fun obj => obj.name))

private def graphDeps? : Option (Array (Array Nat)) :=
  graph?.map (fun g => g.deps)

private def graphInitOrder? : Option (Array Nat) :=
  discovery.toOption.map (fun d => d.initOrder.order.map (fun i => i.val))

private def graphBfsOrder? : Option (Array Nat) :=
  graph?.map (fun g => (Reloc.Symbol.bfsOrder g).map (fun i => i.val))

private def putsProvider? : Option Nat :=
  graph?.bind fun g =>
    (Reloc.Symbol.resolveByName g (Reloc.Symbol.bfsOrder g) "puts").map
      (fun ref => ref.objectIdx.val)

#guard graphNames? == some #["fixture-main", "libc.so.6", "libm.so.6"]
#guard graphDeps? == some #[#[1, 2], #[], #[]]
#guard graphInitOrder? == some #[1, 2, 0]
#guard graphBfsOrder? == some #[0, 1, 2]
#guard putsProvider? == some 1

private def relocPlan : Except String Reloc.Result := do
  let d ← discovery
  Reloc.Result.ofDiscover d

private def mainDataRelocTypes? : Option (Array UInt32) :=
  relocPlan.toOption.bind fun rp =>
    let mainIdx : Fin rp.graph.objects.size := ⟨0, rp.graph.sizePos⟩
    if hSeg : 1 < rp.graph.objects[mainIdx].elf.segments.items.size then
      let dataIdx : Fin rp.graph.objects[mainIdx].elf.segments.items.size := ⟨1, hSeg⟩
      some ((rp.entries mainIdx dataIdx).map (fun entry => entry.type))
    else
      none

private def mainDataRelocOffsets? : Option (Array Nat) :=
  relocPlan.toOption.bind fun rp =>
    let mainIdx : Fin rp.graph.objects.size := ⟨0, rp.graph.sizePos⟩
    if hSeg : 1 < rp.graph.objects[mainIdx].elf.segments.items.size then
      let dataIdx : Fin rp.graph.objects[mainIdx].elf.segments.items.size := ⟨1, hSeg⟩
      some ((rp.entries mainIdx dataIdx).map (fun entry => entry.r_offset.toNat))
    else
      none

private def mainDataRelocTargets? : Option (Array String) :=
  relocPlan.toOption.bind fun rp =>
    let mainIdx : Fin rp.graph.objects.size := ⟨0, rp.graph.sizePos⟩
    if hSeg : 1 < rp.graph.objects[mainIdx].elf.segments.items.size then
      let dataIdx : Fin rp.graph.objects[mainIdx].elf.segments.items.size := ⟨1, hSeg⟩
      some ((rp.entries mainIdx dataIdx).map (fun entry => entry.target.tag))
    else
      none

private def mainDataRelocProviders? : Option (Array (Option Nat)) :=
  relocPlan.toOption.bind fun rp =>
    let mainIdx : Fin rp.graph.objects.size := ⟨0, rp.graph.sizePos⟩
    if hSeg : 1 < rp.graph.objects[mainIdx].elf.segments.items.size then
      let dataIdx : Fin rp.graph.objects[mainIdx].elf.segments.items.size := ⟨1, hSeg⟩
      some ((rp.entries mainIdx dataIdx).map fun entry =>
        entry.target.symRef?.map (fun ref => ref.objectIdx.val))
    else
      none

#guard mainDataRelocTypes? == some #[8, 6]
#guard mainDataRelocOffsets? == some #[0x1410, 0x1420]
#guard mainDataRelocTargets? == some #["none", "ok"]
#guard mainDataRelocProviders? == some #[none, some 1]

private def withLayout? (f : (rp : Reloc.Result) → Layout.Layout rp.objCount → α) :
    Option α := do
  let rp ← relocPlan.toOption
  let layout ← (Layout.Layout.ofRelocResult rp).toOption
  some (f rp layout)

private def layoutSpan? : Option UInt64 :=
  withLayout? (fun _ layout => layout.totalSpan)

private def layoutAdvances? : Option (Array UInt64) :=
  withLayout? (fun _ layout => layout.elfs.toArray.map (fun elfLayout => elfLayout.advance))

private def layoutBases? : Option (Array UInt64) :=
  withLayout? (fun _ layout => (Layout.assignBases reservationBase layout).toArray)

#guard layoutSpan? == some 0x6000
#guard layoutAdvances? == some #[0x2000, 0x2000, 0x2000]
#guard layoutBases? == some #[0x80000000, 0x80002000, 0x80004000]

private def exampleReservation : Reserve :=
  { addr := reservationBase, len := 0x6000, noWrap := by decide }

private def boundPlan : Except String Finalize.BoundPlan := do
  let rp ← relocPlan
  let layout ← Layout.Layout.ofRelocResult rp
  if h : layout.totalSpan = 0x6000 then
    return {
      rp with
      layout := layout
      rsv := exampleReservation
      h_total := by
        change (0x6000 : UInt64) = layout.totalSpan
        exact h.symm }
  else
    .error "fixture layout span changed"

private def boundPlan? : Option Finalize.BoundPlan :=
  boundPlan.toOption

private def ctorAddrs? : Option (Array UInt64) :=
  boundPlan?.map Finalize.ctorAddrs

private def dtorAddrs? : Option (Array UInt64) :=
  boundPlan?.map Finalize.dtorAddrs

private def loadElfCount? : Option Nat := do
  let bp ← boundPlan?
  let ops ← (Finalize.build bp).toOption
  some ops.elfs.size

private def mainDataStoreAddrs? : Option (Array UInt64) := do
  let bp ← boundPlan?
  let ops ← (Finalize.build bp).toOption
  let mainOps ← ops.elfs[0]?
  let dataOps ← mainOps.segments[1]?
  some (dataOps.stores.map (fun store => store.addr))

private def mainDataStoreValues? : Option (Array UInt64) := do
  let bp ← boundPlan?
  let ops ← (Finalize.build bp).toOption
  let mainOps ← ops.elfs[0]?
  let dataOps ← mainOps.segments[1]?
  some (dataOps.stores.map (fun store => store.value))

#guard ctorAddrs? == some #[0x80000100]
#guard dtorAddrs? == some #[0x80000108]
#guard loadElfCount? == some 3
#guard mainDataStoreAddrs? == some #[0x80001410, 0x80001420]
#guard mainDataStoreValues? == some #[0x80000000, 0x80002220]

end LeanLoad.Examples

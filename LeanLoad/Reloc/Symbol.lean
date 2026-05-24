/-
Symbol resolution.

Spec: gabi 08 § Shared Object Dependencies — for each undefined
reference in any loaded elf, find the providing (object, symbol)
pair by BFS over the dep DAG starting at main.

Pipeline within this module:

  · `Find`   — per-elf lookup. `findInElf` returns
                `Option (MatchedSym elf name)`; the four witnesses
                (in-bounds, isDef, nameEq, isFirst) live as fields,
                so consumers read them directly without separate
                theorem dispatch.
  · `Bfs`    — BFS traversal of `LoadGraph` (`bfsOrder g`), plus
                `bfsOrder_nodup` and `bfsOrder_head` characterisations.
  · `Lookup` — across-elves wrapper. `resolveByName g order name`
                returns the first match along `order`; the
                `resolveByName_*` theorems pin the first-match
                contract abstractly over `order`, so combining
                with `bfsOrder` gives the gabi-08 BFS-resolution
                spec.
`Reloc.Result` uses these helpers to resolve only symbols referenced by dynamic
relocation records.
-/

import LeanLoad.Reloc.Symbol.Find
import LeanLoad.Reloc.Symbol.Bfs
import LeanLoad.Reloc.Symbol.Lookup

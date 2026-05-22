# AGENTS.md

Research project. No backward compatibility required.

## Working style

- Refactor freely. Delete old forms entirely; do not leave aliases,
  `@deprecated` shims, or "removed" comments.
- Don't hunt for the smallest possible diff. If a deeper restructure
  is the right shape, take it — invasive changes are fine as long as
  every touched file ends green. Smallness is not a goal here;
  correctness and clear types are.
- Push properties earlier in the pipeline so witnesses propagate
  through types. Runtime checks downstream of an established fact
  are a smell.
- Cite the spec inline whenever a constant, predicate, or invariant
  comes from one — gabi (`third_party/gabi/docsrc/elf/*.rst`), the
  per-arch psABIs, POSIX, etc. A short `gabi 07 § Program Header`
  reference next to the definition is enough.
- One project goal is to develop a precise specification of an ELF
  loader. Keep properties / invariants that meaningfully describe
  what a stage produces, even when no current downstream consumer
  cites them — they belong to the spec of the stage. If a property
  is unused, ask first whether the *downstream is too weak* (and
  should be strengthened to consume the witness) or whether the
  property is *essential to the correctness of this stage* (e.g.
  "we deduplicated by canonical name", "every NEEDED was resolved
  and recorded") and is worth keeping as a load-bearing invariant
  regardless of who reads it. Drop a property only when it's
  genuinely incidental — not just because no caller happens to use
  it today.

## Debuggability

Three rules that pay off across the project:

1. **`deriving Repr` on every parse / elaborate / plan type.**
   Then `--debug` is structured by construction.
2. **Deterministic output.** No timestamps, no hash-iteration order,
   no addresses chosen by ASLR in the plan. Sort everything that has
   no semantic order — golden tests rely on this.
3. **Failure messages with context, not bare `panic`.** When the
   surrounding logic already knows the offending tag / offset /
   symbol, surface it; don't force the user to grep. Don't reach
   for context that isn't already at hand.

## Tests vs. theorems

Both have a job, and adding one doesn't retire the other:

- **`#guard` checks** colocated with each definition serve *readers*.
  Concrete examples like
  `formula R_X86_64_RELATIVE { B := 0x10000, A := 0xa90, … } = some { value := 0x10a90, size := .b8 }`
  make a function's contract scannable and fail at elaboration time
  if the table moves under them. Use them anywhere a function does
  nontrivial arithmetic, table lookups, formula evaluation, or has
  interesting edge cases (empty inputs, alignment boundaries,
  symbol-less relocations).
- **Theorems live next to the definitions they characterise.** No
  separate `Thm/` tree — the proofs live with the code they're about.

A `#guard` shows *what the function does* on a concrete input; the
theorem shows *what it always does*. The two are complementary
audit surfaces.

## Lean 4 Workflows

Before Lean proof work, build debugging, mathlib search, or larger
Lean refactors, read `third_party/lean4-skills/plugins/lean4/skills/lean4/SKILL.md`
carefully and follow its workflow guidance.

Environment, from the repository root:
- `LEAN4_PLUGIN_ROOT=$PWD/third_party/lean4-skills/plugins/lean4`
- `LEAN4_SCRIPTS=$LEAN4_PLUGIN_ROOT/lib/scripts`
- `LEAN4_REFS=$LEAN4_PLUGIN_ROOT/skills/lean4/references`

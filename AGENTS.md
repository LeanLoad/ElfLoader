# AGENTS.md

Research project. No backward compatibility required.

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

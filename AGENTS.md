# AGENTS.md

Research project. No backward compatibility required.

- Refactor freely. Delete old forms entirely; do not leave aliases,
  `@deprecated` shims, or "removed" comments.
- Push properties earlier in the pipeline so witnesses propagate
  through types. Runtime checks downstream of an established fact
  are a smell.
- Cite the spec inline whenever a constant, predicate, or invariant
  comes from one — gabi (`third_party/gabi/docsrc/elf/*.rst`), the
  per-arch psABIs, POSIX, etc. A short `gabi 07 § Program Header`
  reference next to the definition is enough.

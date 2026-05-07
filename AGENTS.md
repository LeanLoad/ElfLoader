# AGENTS.md

Research project. No backward compatibility required.

- Refactor freely. Delete old forms entirely; do not leave aliases,
  `@deprecated` shims, or "removed" comments.
- Push properties earlier in the pipeline so witnesses propagate
  through types. Runtime checks downstream of an established fact
  are a smell.

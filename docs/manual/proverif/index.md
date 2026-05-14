---
weight: 100
---

# ProVerif backend

This section documents the hax ProVerif backend, which extracts a
subset of Rust into [ProVerif](https://bblanche.gitlabpages.inria.fr/proverif/)
applied-pi calculus models for symbolic protocol verification.

- [Language description](./language.md) — what Rust constructs are
  accepted, what they render to, and the idiomatic patterns that are
  not yet supported.

> **Status.** The ProVerif backend is experimental. Stage 1 (port to
> the rust-engine architecture) is complete; Stage 2 (protocol DSL +
> events/queries + shipped crypto library) is in design. See the
> [language description](./language.md#stage-2-priorities) for the
> prioritized roadmap.

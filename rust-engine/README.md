# Hax Rust Engine

This crate implements an alternative engine for Rust: the main one is implemented in OCaml and is located in `/engine`.
This Rust engine is designed so that it can re-use some bits of the OCaml engine.

The plan is to slowly deprecate the OCaml engine, rewrite most of its components and drop it.

## Usage
The Rust engine supports only one backend for now: `Lean`.

To run it, use the following command:
```bash
cargo hax into lean
```

This crate should implement an AST for which:
 1. Valid (cargo check) pretty-printed Rust can be produced out of it.
 2. The Rust THIR AST from the frontend can be imported into this AST.
 3. The AST defined in the OCaml engine can be imported into this AST.
 4. This AST can be exported to the OCaml engine.
 5. This AST should be suitable for AST transformations.

## Usage
`hax-rust-engine` expects it's stdin to be the output of `cargo hax json`, e.g.:
```bash
cargo hax json -o - | hax-rust-engine > output.rs
```

## Test
`cd tests && ./print.sh` will move `src/main.rs` to `main.rs.bak`, parse and pretty print that main file as `main.rs`, and format it.

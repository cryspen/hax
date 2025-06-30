This crate should implement an AST for which:
 1. Valid (cargo check) pretty-printed Rust can be produced out of it.
 2. The Rust THIR AST from the frontend can be imported into this AST.
 3. The AST defined in the OCaml engine can be imported into this AST.
 4. This AST can be exported to the OCaml engine.
 5. This AST should be suitable for AST transformations.

## Usage
The following command will run hax with the rust engine instead of the ocaml one.
For now, this will create a dummy lean file, regardless the backend provided.

```bash
HAX_ENGINE_BINARY=hax-rust-engine cargo hax into fstar
```

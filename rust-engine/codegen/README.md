# hax-rust-engine-codegen

This internal Rust crate is responsible for generating a rich set of **visitor traits and driver functions** for the HAX abstract syntax tree (AST).

**Why generate these automatically?** Writing visitor code manually for a large and evolving AST is tedious, error-prone, and hard to keep consistent. This crate automates the generation of structurally correct visitors, ensuring that all visitable types are handled uniformly and that traversal logic stays in sync with the AST definition. It also reduces boilerplate and makes adding new traversal patterns as simple as toggling a flag.

## What It Does

The crate:

- **Loads** the full hax AST (`lib.rs`) including all `mod` declarations via a recursive module inlining mechanism.
- **Parses** the syntax tree using [`syn`](https://docs.rs/syn/) and detects types annotated with `#[visitable]`.
- **Generates** code in `src/ast/visitors/generated.rs` that includes:
  - Visitor traits (like `VisitorMapReduceCf`) with configurable behavior.
  - Default driver functions that implement structural traversal.
  - Manual driver stubs for explicitly-handled types.
- **Supports** customization using attributes such as:
  - `#[visitable]`: default handling.
  - `#[visitable(opaque)]`: disables traversal.
  - `#[visitable(manual_driver(...))]`: delegates traversal logic to user-defined code.

## Generated Visitors

For each combination of traversal features, a distinct visitor module is generated. Each visitor kind controls:

| Feature            | Description                                                                 |
|--------------------|-----------------------------------------------------------------------------|
| `map`              | Takes `&mut` references (mutable traversal).                                |
| `reduce`           | Returns a monoidal value (`identity`, `append`).                            |
| `cf`               | Supports short-circuiting with `ControlFlow`.                               |

**Visitor module examples**:
- `visitor_map` – mutable traversal only
- `visitor_reduce` – immutable folding
- `visitor_map_reduce_cf` – mutable traversal with reduction and control-flow

Each visitor:
- Defines a trait (e.g. `VisitorMapReduceCf`) with visit methods for every visitable type.
- Is paired with driver functions like `visit_expr()` to invoke traversal.

## How It Works

### Entry Point

The generator is invoked via `main.rs`:
- Loads and inlines `../src/lib.rs`.
- Collects `#[visitable]` types.
- Generates 9 visitor variants (`2³` combinations + the one without any feature). We probably do not need all the variant: let's see when we will write phases.
- Writes the generated visitor modules to `../src/ast/visitors/generated.rs`.

### Inline Mod Handling

The `ModuleInliner` visitor rewrites external `mod foo;` declarations into inline modules by reading the corresponding `foo.rs` or `foo/mod.rs` files. This allows complete AST analysis in-memory.

### Helpers

The crate includes various utilities in `helpers.rs`, such as:
- Extracting named fields (even for tuple structs).
- Handling Rust generics and where clauses.
- Pretty-printing and formatting with `rustfmt`.

## Output

The generated code is written to `../src/ast/visitors/generated.rs`.
Also, we generate `../src/ast/visitors/generated_manual_templates.rs`: a file with templates for the manual drivers.

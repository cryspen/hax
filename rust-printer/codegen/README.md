# Hax Engine Codegen

This is an internal crate which is used to generate the files in the
`src/ast/generated` and `src/generic_printer/generated` directories of `hax`.

It is currently used to ensure consistency between the engine internal AST and:
 - the `Fragment` and `FragmentRef` enumerations, and
 - the **print view**.

See below for more explanations.

## Usage
Run `cargo run` in this directory. This will write the in the `generated`
directories in `../src`.

## `Fragment` and `FragmentRef` enumerations
The AST of the Rust engine of hax is represented by a certain number of types:
`Ty`, `Expr`, `Item`, `Literal`, etc.

We produce an enumeration `Fragment` that can represent any fragment of the AST, it looks like the following:
```rust
enum Fragment {
    Ty(Ty),
    Expr(Expr),
    Item(Item),
    Literal(Literal),
    ...
}
```

It is very handy for:
 - **diagnostics (error, warnings, etc.)**: an error carries the AST node it failed at;
 - **printing**: while printing the expression `x`, it may be useful to lookup its parent. The parent of `x` may be an expression (e.g. `f x y`), but also a type (e.g. `[u8; x]`) or even a funtion (e.g. `fn f() {x}`). The parent of a fragment of AST may generally be any other fragment of AST.

Writing such a type is very mechanical. Also, it's handy to have `From`
instances, so that e.g. one can lift a `Ty` or a `Expr` into a `Fragment`.
Thus, this crate generates such types.

We derive both an owned version, `Fragment`, and a borrowed one `FragmentRef<'a>`.

## Print View
### Context
Pretty printing requires making decisions about layout: for instance, deciding
whether we should insert parenthesis or not.

Such decision cannot be taken *locally*: when printing a fragment, you need
relative informations. You need to know where the fragment you print is located,
what is surrounding that fragment.

We call those surrounding informations *contextual informations*.

### Solution
For every type of the AST, we create a shallow view of it, that ships with
contextual informations.

We define a type `PrintContext<'a, T>`: a struct that contains a reference `&'a T` and contextual information.

For example:
```rust
enum ExprKind {
    If(bool, Expr, Expr),
}
```

Would be transformed into:
```rust
enum ExprKind<'; a> {
    If(PrintContext<'a, Expr>, PrintContext<'a, Expr>, PrintContext<'a, Expr>),
}
```

This is a very simple transformation: leaving lifetimes aside, basically, for
every field (of every `struct` and every variant of every `enum`), we change
types `T` into `PrintContext<T>`.

Since this is very mechanical, we generate it with this crate. We also generate
utilities to transform AST fragments into their views.

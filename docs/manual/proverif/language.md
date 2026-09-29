---
weight: 103
---

# The hax→ProVerif sub-language

This page describes the Rust sub-language that the hax ProVerif backend
extracts, the ProVerif it produces, and the Rust constructs it cannot
model.

> **Disclaimer.** The ProVerif backend is experimental. See the [open
> issues](https://github.com/cryspen/hax/issues?q=is%3Aissue+state%3Aopen+label%3Aproverif)
> for known limitations.

## Encoding

`cargo hax into proverif` writes two files per crate:

- `lib.pvl`: one declaration per Rust item, with a comment header and a
  `(* src: ... *)` provenance comment on each item.
- `missingdecl.pvl`: a diagnostic listing every symbol `lib.pvl`
  references that is defined neither in `lib.pvl` nor in the shipped
  libraries. It is not part of the model (see
  [below](#missingdeclpvl)).

The model is *uniform-bitstring*:

- **Every Rust type is ProVerif `bitstring`**: integers, booleans,
  strings, tuples, arrays, slices, vectors, references, type parameters
  and associated types alike.
- **Booleans** are the data constructors `True()` / `False()`. A
  condition `c` is tested as `let (=True()) = c in ... else ...`.
- **Integer literals** are opaque constants `nat_N` (`nat_neg_N` when
  negative). String, char and float literals are likewise opaque
  constants (`string_lit__...`, `char_lit__...`, `float_lit__...`).
  Distinct literals are distinct constants.
- **Structs and enum variants** are `fun C(bitstring, ...): bitstring
  [data].` constructors, with one `reduc` accessor per field.
- **Tuples** are the `rust_primitives__hax__TupleN__TupleN` data
  constructors, with projectors.
- **Arrays, slices, vectors and iterators** are cons-lists over
  `rust_primitives__hax__array_cons` / `array_nil`.
- **`Option`** uses the `Some(x)` / `None()` constructors. **`Result`**
  is transparent: `Ok(x)` renders as `x` and `Err(_)` as
  `bitstring_err()`, the failing sink.

Scalar values are thus opaque symbolic terms, while term structure
(constructors, calls, control flow) is preserved. Crypto and
serialization are given meaning by the shipped libraries and by
annotations (see [Crypto and external functions](#crypto-and-external-functions)).

## Supported Rust

| Rust | ProVerif |
|---|---|
| `fn f(p1: T1, ..., pn: Tn) -> T { body }` | `letfun f(p1: bitstring, ..., pn: bitstring) = body.` |
| `fn f() -> T`, `const`, `static`, associated `const` | `const f: bitstring.` (a `fun` of the observed arity if a use site applies it) |
| `struct` / `enum` | `[data]` constructors + `reduc` field accessors |
| `impl` blocks | each method flattened to a top-level `letfun`, ordered so dependencies come first |
| `trait`, `type` alias, `use` | nothing emitted |
| `mod m { ... }` | flattened into the single `lib.pvl`; paths joined with `__` |
| `let pat = e; body` | `let pat = e in body` (with `else bitstring_err()` when `pat` is refutable) |
| `if c { a } else { b }` | `let (=True()) = c in a else b` |
| `match` | a `let pat = scrutinee in ... else ...` chain ending in `bitstring_err()` |
| match guards `pat if cond` | the guard is tested inside the arm; on failure the next arm is tried |
| or-patterns `A \| B` | one arm per alternative |
| `expr?` | desugared to a `match` |
| early `return` / `break` / `continue` | functionalized into `if` / `match` |
| `let mut`, `&mut` arguments, field assignment | threaded functionally; rebound names are renamed `x`, `x_1`, `x_2`, ... |
| `&e`, `*e`, blocks, lifetimes | erased |
| `for x in coll { ... }` | unrolled to a fixed depth (`LOOP_BOUND` in the backend); a longer run yields `bitstring_err()` |
| `fold`, `find`, `any`, `find_map`, `filter_map`, `for_each`, `.map(..).collect()`, `Option::map`, `bool::then` applied to a closure | rewritten to the bounded `for` unrolling or to a `match` / `if` |
| `[a, b, c]` | `array_cons(a, array_cons(b, array_cons(c, array_nil())))` |
| trait method calls with a concrete `Self` type | resolved to the concrete impl method |
| `x && y`, `x \|\| y` | opaque `logical_and(x, y)` / `logical_or(x, y)` |
| `Clone::clone`, `Into::into`, `Deref::deref`, unsizing, `as` casts | identity |

Integer arithmetic and comparisons render as the `rust_primitives__hax__machine_int__*`
operators declared in `primitives.pvl`. `==` / `!=` are structural
equality of terms; `+ 1` / `- 1` reduce over `nat_0 .. nat_16`; every
other operator is an opaque constructor. `primitives.pvl` also provides
an opt-in reductive layer (`nat_add`, `nat_sub`, `nat_lt`, `nat_le`,
`nat_gt`, `nat_ge`) that evaluates on two constants in
`nat_0 .. nat_16`, for use in handwritten processes and queries.

## Unsupported Rust

Rejected with a diagnostic, stopping extraction of the item:

- `unsafe` blocks, raw pointers, `dyn Trait`
- assignments to a non-trivial place (`a[i].f = x` and similar)

Rendered as `bitstring_err()` with a diagnostic and an inline
`(* ... *)` comment, keeping the rest of the model well formed:

- `while` and `loop`
- closures not consumed by one of the combinators above, and
  functions or constructors passed as values
- `if let` chains (`if let A = a && let B = b`)
- array patterns (rendered as a wildcard)

Other limitations:

- **Recursion.** A function in a call-graph cycle has no `letfun`
  encoding; it is rejected with a diagnostic and declared as an
  uninterpreted `fun` so its callers still resolve.
- **Generics.** Generic functions are not monomorphized; type
  parameters collapse to `bitstring`. Trait calls on a generic `Self`
  stay calls to the trait method.
- **`x @ p` patterns** bind `x`; the sub-pattern `p` is not tested.
- **`Result` errors** all become `bitstring_err()`, so distinct error
  variants are indistinguishable in the model.
- **Numeric widths and overflow** are not modeled.

## Crypto and external functions

### Shipped libraries

Two libraries ship in `hax-lib/proof-libs/proverif/` and are loaded
with `-lib` ahead of `lib.pvl`:

- **`primitives.pvl`** declares the symbols extracted code relies on:
  the public channel `c`, `construct_fail`, `bitstring_default` /
  `bitstring_err`, `Some` / `None`, `True` / `False`, `nat_0 .. nat_16`,
  `logical_and` / `logical_or`, the tuple and cons-list constructors,
  the integer operators, and models of common `core` / `alloc` items
  (options, slices, vectors, iterators, conversions, panics).
- **`cryptolib.pvl`** is a Dolev-Yao model of standard primitives, all
  over `bitstring`: hash (`crypto__hash`), AEAD in combined and detached
  form, KDF / HKDF, Diffie-Hellman, KEM, signatures, MAC, and injective
  serialization (`crypto__serialize`, `crypto__serialize_tagged`).
  One-way functions are opaque `fun`s; decryption, verification and
  parsing are partial `reduc` destructors.

```bash
proverif -lib primitives.pvl -lib cryptolib.pvl -lib lib.pvl model.pv
```

### Annotations

A Rust crypto wrapper is connected to the libraries by replacing its
body, keeping the protocol code plain Rust:

```rust
#[hax_lib::proverif::replace_body("crypto__aead_enc(key, pt, ad)")]
fn encrypt(key: &Key, pt: &[u8], ad: &[u8]) -> Vec<u8> { ... }
```

| Annotation | Effect |
|---|---|
| `#[hax_lib::proverif::replace_body("...")]` | replace the function body with the given ProVerif term |
| `#[hax_lib::proverif::replace("...")]` | replace the whole item with the given ProVerif |
| `#[hax_lib::proverif::before("...")]` / `after("...")` | emit ProVerif before / after the item |
| `hax_lib::proverif!("...")` | a ProVerif term in expression position |
| `#[hax_lib::pv_extern]` | declare `fun extern__<fn>(bitstring, ...): bitstring.` and make the body call it |
| `#[hax_lib::pv_stub("...")]` | shorthand for `proverif::replace_body("...")` |
| `#[hax_lib::pv_inverse_of(other)]` | replace the item with `reduc forall x: bitstring; self(other(x)) = x.` |
| `#[hax_lib::pv_inline]` | inline every call to this function at the call site; the function itself is not emitted |
| `#[hax_lib::pv_constructor]` | render the function as a `[data]` constructor |
| `#[hax_lib::pv_handwritten]` | render the body as `bitstring_default()`, marked for a handwritten model |
| `#[hax_lib::opaque]` | on a function, an opaque `[data]` constructor; on a type, nothing |

Inside the quoted strings, `${path}` refers to a Rust item by path and
is rendered as its ProVerif name.

`#[hax_lib::process_init]`, `process_read`, `process_write` and
`protocol_messages` are parsed, not rendered: annotated items extract
as ordinary items. The `hax-lib-protocol` and `hax-lib-protocol-macros`
crates provide a state-machine API (`InitialState`, `WriteState`,
`ReadState`) whose `#[init]`, `#[init_empty]`, `#[write]` and `#[read]`
macros attach these attributes.

## `missingdecl.pvl`

Every symbol referenced by `lib.pvl` and declared neither there nor in
`primitives.pvl` is declared in `missingdecl.pvl`, without `[data]`,
together with the items that reference it. This includes integer
literals above `nat_16` and other literal constants. Each entry is
either defined (by hand, by an annotation, or by extracting the crate
that owns it) or deliberately left abstract as an ideal-functionality
boundary.

## Scoping extraction

With no `-i` clauses every item is a root and is emitted. To keep only
the protocol under study, narrow `-i` to its entry points; their
transitive dependencies are included:

```bash
cargo hax into -i '-** +your_crate::protocol::**' proverif
```

The dependency graph is built over the source call graph, before
`proverif::replace_body` rewrites a body, so a helper called only by a
replaced body is still emitted. Exclude it with an explicit `-NAME` if
it is unwanted.

## Testing

ProVerif tests are ordinary modules of the `tests` crate, under
`tests/src/`, including the `tests/src/legacy/proverif-*` modules.
Expected diagnostics are declared with `//! @fail(extraction):
proverif(...)` directives, and other backends are switched off with
`//! @off: ...`. Extracted models are committed as snapshots under
`tests/snapshots/**/proverif/`.

```bash
just test -b proverif
# equivalently
cargo run --release --bin test-driver -- ./tests -b proverif
```

For each module the test driver extracts the model into its snapshot
directory and runs the ProVerif parse check (`run_proverif` in
`cli/test-driver/src/commands.rs`): `proverif -parse-only` loads
`primitives.pvl`, `cryptolib.pvl`, `missingdecl.pvl` and the model as
libraries against an empty process, catching syntax errors, undefined
or duplicate names, and arity mismatches. `--no-verify` skips the parse
check.

`examples/proverif-psk` is a worked example with a hand-written
analysis file.

## Pointers to source

| What | Where |
|---|---|
| Printer and file layout | `rust-engine/src/backends/proverif.rs` |
| Phase pipeline | `fn phases` in `rust-engine/src/backends/proverif.rs` |
| ProVerif-specific phases | `rust-engine/src/phase/proverif_*.rs` |
| Shipped libraries | `hax-lib/proof-libs/proverif/` |
| Annotation macros | `hax-lib/macros/src/lib.rs`, `hax-lib/macros/src/implementation.rs` |
| Test modules and snapshots | `tests/src/`, `tests/snapshots/` |

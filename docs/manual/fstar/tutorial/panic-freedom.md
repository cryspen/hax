---
weight: 0
---

# Panic freedom

Let's start with a simple example: a function that squares a `u8`
integer. To extract this function to F\* using hax, we simply need to
run the command `cargo hax into fstar` in the directory of the crate
in which the function `square` is defined.

*Note: throughout this tutorial, you can edit the snippets of code and
extract to F\* by clicking the play button (:material-play:), or even typecheck it with the button (:material-check:).*

```{.rust .playable .expect-failure }
fn square(x: u8) -> u8 {
    x * x
}
```

Though, if we try to verify this function, F\* would flag a
subtyping issue: that is, F\* tells us that it is not able to 
prove that the result of the multiplication `x * x` fits within the 
range of `u8`. The multiplication `x * x` may indeed be overflowing!

For instance, running `square(16)` panics: `16 * 16` is `256`, which
is just over `255`, the largest integer that fits `u8`. Rust does not
ensure that functions are *total*: this means that a function may 
panic at any point, or may never terminate.

## Rust and panicking code
Quoting the chapter [To `panic!` or Not to
`panic!`](https://doc.rust-lang.org/book/ch09-03-to-panic-or-not-to-panic.html)
from the Rust book:

> The `panic!` macro signals that your program is in a state it can't
> handle and lets you tell the process to stop instead of trying to
> proceed with invalid or incorrect values.

That is, a Rust program should panic only when a logical assumption 
or invariant is violated. A panic represents a **controlled failure** 
in response to an *invalid* program state.

Rust's type system already prevents undefined behavior (UB) through 
its ownership and borrowing rules. Formal verification with hax goes 
even further:  it proves that logical errors leading to `panic`s 
cannot occur either.

In other words:
- Rust's type system → No memory unsafety (no undefined behavior)
- Formal verification → No panics (and thus stronger 
correctness guarantees)

From this observation emerges the urge of proving Rust programs 
to be panic-free!

## Fixing our `square(x: u8) -> u8` function
Let's come back to our initial example. There exists an informal 
assumption that we make about the multiplication operator in Rust: 
the inputs should be small enough for the multiplication 
operation to not overflow.

Note that Rust also provides `wrapping_mul()` (as part of 
`std::intrinsics`), a non-panicking variant of the multiplication 
on `u8` that wraps around when the result is bigger than `255`. 
For values `x: u8` and `y:u8`, this is equivalent to `(x * y) mod 256`. 

Replacing the usual multiplication operator with `wrapping_mul()` 
in `square` would fix the panic:
``` {.rust .playable}
fn square(x: u8) -> u8 {
    x.wrapping_mul(x)
}
```

However, observe that `square(16)` (with `wrapping_mul()`) returns zero! 
The function is mathematically incorrect for inputs > 15, 
even though it doesn't panic.

Wrapping arithmetic is useful for many things: 
1. Hash functions (where overflow is expected)
2. Checksums (CRC, etc.)
3. Cryptography (where modular arithmetic is intentional)
4. Performance-critical code (avoiding overflow checks)

But for `square`, it's semantically wrong: this is not what one 
would mathematically expect from the `square` function.

Thus, our problem is that our function `square` is well-defined only when
its input is within `0` and `15`.

### Solution A: Reflect the "partialness" of the function in Rust
The first solution is to take advantage of the built-in Rust `Option<T>` type, 
and make `square` return an `Option<u8>` instead of a `u8`:
``` {.rust .playable}
fn square_option(x: u8) -> Option<u8> {
    if x >= 16 {
        None
    } else {
        Some(x * x)
    }
}
```

> **What is Option<T>?**
>
> The type `Option` represents an optional value: every `Option` is either 
> `Some` and contains a value, or `None`, and does not.
>
> `Option<T>` is Rust's way of encoding **partial functions** (functions that 
> aren't defined for all possible inputs). Instead of panicking on invalid inputs,
> the function returns `None`, making the "partiality" **explicit in the type signature**.
> Rust also provides convenient combinators like `.map()`, `.and_then()`, etc.

Here, F\* is able to prove panic-freedom: calling `square` with any
input is safe. Though, one may argue that `square`'s input being small
enough should really be an assumption. Having to deal with the
possible integer overflowing whenever squaring is a huge burden. Can
we do better?

### Solution B: Add a Pre-condition
Rust's type system doesn't directly allow the programmer to formalize the
assumption that `square()` expects a small `u8`. This becomes
possible using hax: one can annotate a function with a pre-condition
on its inputs!

The pre-conditions and post-conditions on a function form a
*contract*: "if you give me some inputs that satisfies a given formula
(_the "pre-condition"_), I will produce a return value that satisfy
another formula (_the "postcondition"_)". Outside this contract,
(for all we know) anything might happen: the function might panic, 
it might run forever, erase your disk, etc.

The helper crate
[hax-lib](https://github.com/cryspen/hax/tree/main/hax-lib)
provides the `hax_lib::requires(...)`
[procedural macro (proc-macro)](https://doc.rust-lang.org/reference/procedural-macros.html)
which lets user writing pre-conditions directly in Rust.

```{.rust .playable}
#[hax_lib::requires(x < 16)]
fn square_requires(x: u8) -> u8 {
    x * x
}
```

With this precondition, F\* is able to prove panic freedom. From now
on, it is the responsibility of the clients of `square` to respect the
contract. The next step is thus be to verify, through hax extraction,
that `square` is used correctly at every call site.

## Common panicking situations
Multiplication is not the only "panicking function" provided by the Rust
library: most of the other integer arithmetic operation have such
informal assumptions.

Another source of panics is **indexing**. Indexing in an array, a slice or
a vector is a partial operation: the index might be out of range.

Another solution for safe indexing is to use the [newtype index
pattern](https://matklad.github.io/2018/06/04/newtype-index-pattern.html),
which is [also supported by
hax](https://github.com/cryspen/hax/blob/d668de4d17e5ddee3a613068dc30b71353a9db4f/tests/attributes/src/lib.rs#L98-L126). The [data invariants](data-invariants.md#newtype-and-refinements) chapter gives more details about this.

## Example: Proving Panic Freedom in ChaCha20

In the `/examples` subdirectory of hax codebase, you can find [an example 
implementation of `ChaCha20`](https://github.com/cryspen/hax/blob/main/examples/chacha20/src/lib.rs)
that makes use of pre-conditions to prove panic freedom in your code.

For reference, [ChaCha20](https://en.wikipedia.org/wiki/Salsa20#ChaCha_variant) is a stream cipher developed by Daniel J. Bernstein, derived from from the closely-related Salsa20 stream cipher.

### Potential source of panic

Consider this specific function in `/examples/chacha20/src/lib.rs`:
```rust
#[hax::requires(plain.len() <= 64)]
pub fn chacha20_encrypt_last(st0: State, ctr: u32, plain: &[u8]) -> Vec<u8> {
    let mut b: Block = [0; 64];
    b = update_array(b, plain);  // Note: This line would panic if plain.len() > 64
    b = chacha20_encrypt_block(st0, ctr, &b);
    b[0..plain.len()].to_vec()
}
```

This function relies on a helper function in `src/hacspec_helper.rs`: 
```rust
pub(super) fn update_array(mut array: [u8; 64], val: &[u8]) -> [u8; 64] {
    // <const L: usize>
    assert!(64 >= val.len()); // Pay close attention to this line in particular
    for i in 0..val.len() {
        array[i] = val[i];
    }
    array
}
```

What `update_array(mut array: [u8; 64], val: &[u8]) -> [u8; 64]` does is the following: 
- Takes a copy of a 64-byte array (note: `mut array` not `&mut`)
- Takes a borrowed slice of bytes (`val: &[u8]`) of any length
- Most importantly, it asserts `val` isn't longer than 64 bytes (**AND panics if it is!**)
- Copies bytes from `val` into the beginning of `array`
- Leaves the rest of `array` unchanged (keeps original values past `val.len()`)
- Returns the modified `array`

The pre-condition `#[hax::requires(plain.len() <= 64)]` in the `chacha20_encrypt_last(...)` 
function statically proves (in F\*) that the `assert!(64 >= val.len())` in the 
`update_array(...)` helper function will never fail.

**This successfully achieves panic-freedom!**

### Implicit Pre-conditions

Note that not all pre-conditions are or need to be explicit! Consider this implicit pre-condition: 
```rust
type StateIdx = hax_bounded_integers::BoundedUsize<0, 15>;
```
This is a **refinement type** (from the data invariants chapter!) that guarantees indices are in `[0, 15]`.

Notice that every use of `StateIdx` is associated with an implicit pre-condition: 
```rust
fn chacha20_line(a: StateIdx, b: StateIdx, d: StateIdx, s: u32, m: State) -> State {
    let mut state = m;
    state[a] = state[a].wrapping_add(state[b]);  // This is SAFE: a, b, d guaranteed to be < 16
    state[d] = state[d] ^ state[a];
    state[d] = state[d].rotate_left(s);
    state
}
```

Without the `StateIdx` refinement type, we would need a more verbose implementation:
```rust
#[hax::requires(a < 16 && b < 16 && d < 16)]
fn chacha20_line(a: usize, b: usize, d: usize, s: u32, m: State) -> State {
    // ...
}
```

This example doesn't just show how to prove panic freedom in a reliable and productive way. What is really happening is much more subtle: when encoding the precondition using refinement types, the precondition is **moved into the type**, so you don't see `#[requires(...)]` everywhere! `StateIdx` ensures all array indices are valid!

- **The traditional way (rather verbose)**: 
```rust
#[hax::requires(i0 < 16 && i1 < 16 && i2 < 16 && i3 < 16)]
fn quarter_round(i0: usize, i1: usize, i2: usize, i3: usize, state: State) -> State {
    ...
}
```
- **The refinement types approach (much more clean)**: 
```rust
fn quarter_round(i0: StateIdx, i1: StateIdx, i2: StateIdx, i3: StateIdx, state: State) -> State {
    ...
}
```

> **What about `hax_lib::assume!`? How are they handled?**
>
> These are NOT pre-conditions! They're **assumptions to help F\* prove the function is panic-free**. 
> They roughly mean: "*I, the programmer, know this fact is true here, and I'm helping F\* understand the loop invariant.*"
> They are added purely to simply the task of the proof assistant and should be used with extreme care and due diligence.

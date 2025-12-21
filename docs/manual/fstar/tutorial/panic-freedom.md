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

- *Rust's type system* → No memory unsafety (no undefined behavior)
- *Formal verification* → No panics (and thus stronger 
correctness guarantees)

From this observation emerges the urge of proving Rust programs 
to be panic-free!

## Fixing our `square(x: u8) -> u8` function
Let's come back to our initial example. There exists an informal 
assumption that we make about the multiplication operator in Rust: 
the inputs should be small enough for the multiplication 
operation to not overflow.

Note that Rust also provides `wrapping_mul()`[^wrapping-mul], 
a non-panicking variant of the multiplication on `u8` that 
wraps around when the result is bigger than `255`. 
For values `x: u8` and `y:u8`, this is equivalent to `(x * y) mod 256`. 

[^wrapping-mul]:
    `wrapping_mul()` is a stable method available directly on all integer types 
    (`u8`, `u16`, `u32`, etc.) without any imports or feature flags. While wrapping 
    arithmetic operations were [originally part of the unstable `std::intrinsics` module](https://doc.rust-lang.org/std/intrinsics/fn.wrapping_mul.html), they were stabilized and moved to be inherent methods on integer types, making them part of Rust's stable API.

Replacing the usual multiplication operator with `wrapping_mul()` 
in `square` would fix the panic:
```rust
fn square(x: u8) -> u8 {
    x.wrapping_mul(x)
}
```

> **Current Limitation**: `u8::wrapping_mul` is not yet supported in hax's F\* backend[^wrapping-mul-limitation], 
> i.e. while this function won't panic, hax's F\* backend cannot verify it. 
> 
> Use explicit modular arithmetic as a workaround:
> ``` {.rust .playable}
> fn square_wrapping(x: u8) -> u8 {
>     let result = (x as u16) * (x as u16);
>     (result % 256) as u8
> }
> ```

[^wrapping-mul-limitation]:
    While `wrapping_mul()` is a standard Rust method available on all integer types, 
    hax's F\* proof libraries currently lack the definition for `impl_u8__wrapping_mul`. 
    Wrapping multiplication *is* implemented for signed types like `i16` 
    and `i64`, and other wrapping operations like `wrapping_add` and `wrapping_sub` 
    work for `u8`. This is an incomplete implementation rather than a 
    fundamental limitation. If you attempt F\* extraction, you'll see: 
    "`Identifier impl_u8__wrapping_mul not found in module Core_models.Num`". 
    
    The workaround using explicit `(x as u16) * (x as u16) % 256` achieves identical 
    semantics and verifies successfully in F\*.

Observe, however, that `square(16)` (with `wrapping_mul()`) returns zero! 
The function is mathematically incorrect for inputs > 15, 
even though it doesn't panic.

Wrapping arithmetic is useful in many instances where high assurance code would be relevant, 
such as hash functions (where overflows are expected), cryptography (where modular arithmetic 
is intentional), and performance-critical code that aims to avoid overflow checks.

But specifically for `square`, it's semantically wrong: this is not what one 
would mathematically expect from the `square` function.

Thus, we conclude that the main problem is our function `square` only being well-defined when
its input is within `0` and `15`. Let's fix that!

### Solution A: Reflect the "partialness" of the function in Rust
The first solution to this issue is to take advantage of the built-in Rust `Option<T>` type, 
and make `square()` return an `Option<u8>` instead of a `u8`:
``` {.rust .playable}
fn square_option(x: u8) -> Option<u8> {
    if x >= 16 {
        None
    } else {
        Some(x * x)
    }
}
```

> [**What is `Option<T>`?**](https://doc.rust-lang.org/std/option/)
>
> The type `Option` represents an optional value: every `Option` is either 
> `Some` and contains a value, or `None`, and does not.
>
> `Option<T>` is Rust's way of encoding **partial functions**[^partial-fn]. Instead of panicking on invalid inputs,
> the function returns `None`, making the "partiality" **explicit in the type signature**.
> Rust also provides convenient combinators like `.map()`, `.and_then()`, etc.

[^partial-fn]: 
    A **partial function** is one which may be undefined for some inputs, as opposed to a total function which is defined for all possible inputs in its domain. 
    
    For a mathematical treatment of total and partial functions, see: 
    Christopher Hollings (2014). [*Mathematics across the Iron Curtain: A History 
    of the Algebraic Theory of Semigroups*](https://books.google.com/books?id=O9wJBAAAQBAJ&pg=PA233). American Mathematical Society. p. 233. ISBN 978-1-4704-1493-1.

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
which allows users to write hax pre-conditions directly in Rust: 
```{.rust .playable}
#[hax_lib::requires(x < 16)]
fn square_requires(x: u8) -> u8 {
    x * x
}
```

With this precondition, F\* is able to prove panic freedom. From now
on, it is the responsibility of the "clients" of `square` to respect the
contract. Thus, the next step is to verify that `square` is used correctly at every call site.

## Common panicking situations
Multiplication is not the only "panicking function" provided by the Rust
library: most of the other integer arithmetic operation have such
informal assumptions.

For instance, another common source of panics is **indexing**. Indexing in an [array](https://doc.rust-lang.org/book/ch03-02-data-types.html#the-array-type), a [slice](https://doc.rust-lang.org/book/ch04-03-slices.html) or
a [vector](https://doc.rust-lang.org/book/ch08-01-vectors.html#storing-lists-of-values-with-vectors) is a **partial operation**: the index might simply be out of range.

In hax's examples directory (`/examples/chacha20/`), you can find [an example 
implementation of `ChaCha20`](https://github.com/cryspen/hax/blob/main/examples/chacha20/src/lib.rs)
that makes use of pre-conditions to prove panic freedom in your code.

Another solution for safe indexing is to use the [newtype index
pattern](https://matklad.github.io/2018/06/04/newtype-index-pattern.html),
which is [also supported by
hax](https://github.com/cryspen/hax/blob/d668de4d17e5ddee3a613068dc30b71353a9db4f/tests/attributes/src/lib.rs#L98-L126). The [data invariants](data-invariants.md#newtype-and-refinements) chapter gives more details about this.

## Example: Array Helper with Pre-conditions

Here's a simple example that demonstrates the principles we have seen so far:
```rust
fn copy_into_buffer(buffer: &mut [u8; 10], data: &[u8]) {
    assert!(data.len() <= 10);  // This would panic if data is too long
    for i in 0..data.len() {
        buffer[i] = data[i];
    }
}

#[hax_lib::requires(data.len() <= 10)]
fn copy_into_buffer_safe(buffer: &mut [u8; 10], data: &[u8]) {
    for i in 0..data.len() {
        buffer[i] = data[i];  // F* proves this is safe!
    }
}
```

The pre-condition `#[requires(data.len() <= 10)]` statically proves the loop bounds are safe.

## Example: Proving Panic Freedom in ChaCha20

To illustrate how pre-conditions prove panic-freedom in real-world cryptographic code, 
we'll examine the **ChaCha20[^chacha20] implementation from hax's examples directory** 
([`/examples/chacha20/`](https://github.com/cryspen/hax/tree/main/examples/chacha20)). 
This is an actual working example provided by the hax project to demonstrate these techniques.

To show how hax proves panic-freedom in performance-critical cryptographic primitives, let's focus on two key aspects: 

1. **Explicit pre-conditions** (using `#[hax::requires(...)]`) preventing buffer overflows. 
2. **Refinement types** ("implicit" pre-conditions) eliminating array indexing panics

[^chacha20]:
  **ChaCha20** is a high-speed stream cipher designed by Daniel J. Bernstein as a 
  variant of the Salsa20 cipher. It's widely used in modern cryptography, notably 
  in TLS 1.3, WireGuard VPN, and SSH, due to its combination of strong security 
  properties and efficient software implementation. ChaCha20 processes data in 
  64-byte blocks using a 256-bit key and operates through a series of quarter-round 
  functions that mix state through addition, XOR, and rotation operations.
  Reference: Bernstein, Daniel J. (2008). "ChaCha, a variant of Salsa20." 
  [https://cr.yp.to/chacha.html](https://cr.yp.to/chacha.html)

### Explicit Pre-conditions

The ChaCha20 example implementation uses a helper function that copies bytes from a variable-length 
slice into a fixed 64-byte array (from `/examples/chacha20/src/hacspec_helper.rs`)[^pub-super]:
```rust
fn update_array(mut array: [u8; 64], val: &[u8]) -> [u8; 64] {
    assert!(64 >= val.len()); // Note: this panics if val is too long!
    for i in 0..val.len() {
        array[i] = val[i];
    }
    array
}
```

*Notice that this helper function would panic if `val.len() > 64`. As a standalone function without preconditions, F\* cannot prove the assertion will never fail.*

[^pub-super]:
    In the actual hax ChaCha20 implementation, this function is declared as 
    `pub(super) fn update_array(...)`, where `pub(super)` means "visible to the 
    parent module only." However, playground snippets run as top-level code without 
    a module hierarchy, so `pub(super)` would cause a compilation error 
    ("too many leading `super` keywords"). In these tutorial examples, we use 
    `fn` (private function) instead, which behaves identically for demonstration 
    purposes.

What `update_array(mut array: [u8; 64], val: &[u8]) -> [u8; 64]` does is precisely the following: 

- Takes a copy of a 64-byte array (note: `mut array` not `&mut`)
- Takes a borrowed slice of bytes (`val: &[u8]`) of any length
- Most importantly, it asserts `val` isn't longer than 64 bytes (**AND panics if it is!**)
- Copies bytes from `val` into the beginning of `array`
- Leaves the rest of `array` unchanged (keeps original values past `val.len()`)
- Returns the modified `array`

Now consider how this is used in the main encryption function (from `/examples/chacha20/src/lib.rs`):
``` {.rust .playable .expect-failure}
# type State = [u32; 16];
# type Block = [u8; 64];
# // Include update_array in the hidden section!
# fn update_array(mut array: [u8; 64], val: &[u8]) -> [u8; 64] {
#     assert!(64 >= val.len());
#     for i in 0..val.len() {
#         array[i] = val[i];
#     }
#     array
# }
# fn to_le_u32s_16(bytes: &[u8]) -> [u32; 16] {
#     let mut out = [0; 16];
#     for i in 0..16 {
#         out[i] = u32::from_le_bytes(bytes[4 * i..4 * i + 4].try_into().unwrap());
#     }
#     out
# }
# fn u32s_to_le_bytes(state: &[u32; 16]) -> [u8; 64] {
#     let mut out = [0; 64];
#     for i in 0..state.len() {
#         let tmp = state[i].to_le_bytes();
#         for j in 0..4 {
#             out[i * 4 + j] = tmp[j];
#         }
#     }
#     out
# }
# fn xor_state(mut state: State, other: State) -> State {
#     for i in 0..16 {
#         state[i] = state[i] ^ other[i];
#     }
#     state
# }
# fn add_state(mut state: State, other: State) -> State {
#     for i in 0..16 {
#         state[i] = state[i].wrapping_add(other[i]);
#     }
#     state
# }
# type StateIdx = hax_bounded_integers::BoundedUsize<0, 15>;
# fn chacha20_line(a: StateIdx, b: StateIdx, d: StateIdx, s: u32, m: State) -> State {
#     let mut state = m;
#     state[a] = state[a].wrapping_add(state[b]);
#     state[d] = state[d] ^ state[a];
#     state[d] = state[d].rotate_left(s);
#     state
# }
# fn chacha20_quarter_round(a: StateIdx, b: StateIdx, c: StateIdx, d: StateIdx, state: State) -> State {
#     let state = chacha20_line(a, b, d, 16, state);
#     let state = chacha20_line(c, d, b, 12, state);
#     let state = chacha20_line(a, b, d, 8, state);
#     chacha20_line(c, d, b, 7, state)
# }
# fn chacha20_double_round(state: State) -> State {
#     state // Simplified but still valid and does not affect type checking
# }
# fn chacha20_rounds(state: State) -> State {
#     let mut st = state;
#     for _i in 0..10 {
#         st = chacha20_double_round(st);
#     }
#     st
# }
# fn chacha20_core(ctr: u32, st0: State) -> State {
#     let mut state = st0;
#     state[12] = state[12].wrapping_add(ctr);
#     let k = chacha20_rounds(state);
#     add_state(state, k)
# }
# fn chacha20_encrypt_block(st0: State, ctr: u32, plain: &Block) -> Block {
#     let st = chacha20_core(ctr, st0);
#     let pl: State = to_le_u32s_16(plain);
#     let encrypted = xor_state(st, pl);
#     u32s_to_le_bytes(&encrypted)
# }
#[hax_lib::requires(plain.len() <= 64)]
pub fn chacha20_encrypt_last(st0: State, ctr: u32, plain: &[u8]) -> Vec<u8> {
    let mut b: Block = [0; 64];
    b = update_array(b, plain); // Note: This would panic if plain.len() > 64
    b = chacha20_encrypt_block(st0, ctr, &b);
    b[0..plain.len()].to_vec()
}
```

Thus, the explicit pre-condition `#[hax::requires(plain.len() <= 64)]` (in the encryption function above) statically proves (in F\*) that the `assert!(64 >= val.len())` in the `update_array(...)` helper function will never fail.

**This successfully achieves panic-freedom! ✓**

> **Note on Playground Limitations**: This example currently fails in the playground due to 
> incomplete `Vec` support in the F* proof libraries (specifically: `Identifier not found: [v']`). 
> However, the fundamental principle remains sound: the explicit pre-condition 
> `#[hax_lib::requires(plain.len() <= 64)]` in the encryption function creates a contract that 
> callers must satisfy. With this guarantee, F\* can statically prove the `assert!(64 >= val.len())` 
> in the helper function will never fail, i.e. no runtime panics possible.
>
> While hax verification tooling is actively developed and battle-tested in production-verified cryptography, e.g. projects like [HACL*](https://github.com/hacl-star/hacl-star), the playground and some library components 
> are still maturing.

### Refinement Types (Implicit Pre-conditions)

Not all pre-conditions require explicit `#[requires(...)]` annotations, they can be encoded directly in the type system! Consider the following "implicit" pre-condition (in `/examples/chacha20/src/lib.rs`): 
```{.rust .playable}
# use hax_bounded_integers;
type StateIdx = hax_bounded_integers::BoundedUsize<0, 15>;
```
This is a **refinement type** (from [the data invariants chapter!](data-invariants.md)) that guarantees indices are in `[0, 15]`.

Notice that every use of `StateIdx` (in `/examples/chacha20/src/lib.rs`) is associated with this implicit pre-condition: 
```{.rust .playable}
# use hax_bounded_integers;
# type State = [u32; 16];
# type StateIdx = hax_bounded_integers::BoundedUsize<0, 15>;
fn chacha20_line(a: StateIdx, b: StateIdx, d: StateIdx, s: u32, m: State) -> State {
    let mut state = m;
    state[a] = state[a].wrapping_add(state[b]);  // This is SAFE: a, b, d guaranteed to be < 16
    state[d] = state[d] ^ state[a];
    state[d] = state[d].rotate_left(s);
    state
}
```

This example doesn't just show how to prove panic freedom in a reliable and productive way. What is really happening is much more subtle: when encoding the precondition using refinement types, the precondition is **moved into the type**. So, you don't see `#[requires(...)]` everywhere, but `StateIdx` ensures that all array indices are valid!

- **The traditional way (rather verbose)**: 
```{.rust .playable}
# type State = [u32; 16];
#[hax_lib::requires(i0 < 16 && i1 < 16 && i2 < 16 && i3 < 16)]
fn quarter_round_verbose(i0: usize, i1: usize, i2: usize, i3: usize, state: State) -> State {
    state // Simplified (for illustration purposes)
}
```
- **The refinement types approach (much more clean)**: 
```{.rust .playable}
# use hax_bounded_integers;
# type State = [u32; 16];
# type StateIdx = hax_bounded_integers::BoundedUsize<0, 15>;
fn quarter_round_clean(i0: StateIdx, i1: StateIdx, i2: StateIdx, i3: StateIdx, state: State) -> State {
    state // Simplified (for illustration purposes)
}
```

### Why Refinement Types Matter

This example demonstrates a crucial insight: **pre-conditions can be encoded in types**!

Instead of repeating `#[requires(i < 16)]` on every function, we define `StateIdx` once:
```rust
type StateIdx = hax_bounded_integers::BoundedUsize<0, 15>;
```

Now **every** function accepting `StateIdx` automatically gets the bounds check, no 
annotation needed. This is not just a syntactical convenience: we completely shifted from 
*proving properties about functions* to *proving properties about data*.

| Approach | Pre-conditions per function | Type safety |
|----------|----------------------------|-------------|
| Explicit `#[requires(...)]` | Many | Runtime-checked |
| Refinement types | Zero (in the type itself!) | Compile-time guaranteed |

### Pre-conditions, Refinement Types, and Assumptions: What's the Difference?

By now, we have seen two ways to help F\* verify panic-freedom:

1. **(Explicit) pre-conditions** (`#[requires(...)]`): contracts that *callers* must prove. 
2. **Refinement types** (`StateIdx`): invariants encoded directly in *types*. 

But there's a third mechanism you might encounter: **assumptions**.

#### What are `hax_lib::assume!` statements?

These are NOT pre-conditions! They're **hints to help F\* understand intermediate facts** during verification. Unlike the previous two mechanisms, assumptions don't create obligations for callers or constraints in types, they simply tell F\* "*trust me, this fact is true here*."

> **Summary:**
> 
> - **Pre-conditions** (`#[requires(...)]`): contracts that *callers* must prove. 
> - **Refinement types** (e.g., `StateIdx`): invariants that *types* guarantee. 
> - **Assumptions** (`hax_lib::assume!(...)`): facts that *you assert* to help F\*.

#### Example: Loop Invariants in ChaCha20

Consider a part of the `chacha20_update` function from `/examples/chacha20/src/lib.rs`:
```rust
for i in 0..num_blocks {
    let b = chacha20_encrypt_block(st0, i as u32, &m[64 * i..(64 * i + 64)].try_into().unwrap());
    hax_lib::assume!(blocks_out.len() == i * 64);  // Helps F* track the loop invariant
    blocks_out.extend_from_slice(&b);
}
hax_lib::assume!(blocks_out.len() == num_blocks * 64);  // Asserts what we know after the loop
```

Here, the assumptions help F\* understand that the vector length grows predictably: after each iteration `i`, the length is exactly `i * 64` bytes. Without these hints, F\* might not be able to prove that subsequent operations are safe at all, *even though* we (as programmers) know the invariant holds.

> **CAUTION: Use with extreme care!** An incorrect assumption can make F\* verify unsound code. 
> Unlike pre-conditions (which *shift the burden of proof to callers*) and refinement types 
> (which are *enforced by the type system*), assumptions are taken on faith. If you assume 
> something false, you've broken the verification guarantees!

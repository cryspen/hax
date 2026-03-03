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

```{.rust .playable .expect-failure}
fn square(x: u8) -> u8 {
    x * x
}
```

Though, if we try to verify this function, F\* would flag a
subtyping issue: 
```
* Error 19 at Playground.fst(6,31-6,32):
  - Subtyping check failed
  - [...]
  - The SMT solver could not prove the query. [...]
```

That is, F\* tells us that it is not able to 
prove that the result of the multiplication `x * x` fits within the 
range of `u8`. The multiplication `x * x` may indeed be overflowing!

For instance, running `square(16)` panics: `16 * 16` is `256`, which
is just over `255`, the largest integer that fits `u8`. Rust does not
ensure that functions are *total*[^partial-fn] by default: this means that a function may 
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

Rust's type system already prevents **undefined behavior** (UB) through 
its *ownership and borrowing rules*. Formal verification with hax goes 
even further:  it proves that **logical errors leading to a panic 
cannot occur either**.

In other words:

- *Rust's type system* → No memory unsafety (no undefined behavior)
- *Formal verification* → No panics (and thus stronger 
correctness guarantees)

From this observation emerges the urge of proving Rust programs 
to be panic-free!

## Fixing our `square(x: u8) -> u8` function
Let's come back to our initial example. There exists an *informal 
assumption that we make about the multiplication operator* in Rust: 
the **inputs** should be **small enough for the multiplication 
operation to not overflow**. This might be fine for normal, everyday Rust code. 
However, in our journey towards formally guaranteed panic freedom, 
such *assumptions will not be sufficient anymore*. We need to do **more**.

Also note that by default Rust provides `wrapping_mul()`[^wrapping-mul], 
a non-panicking variant of the multiplication on `u8` that 
wraps around when the result is larger than `255`. 
For values `x: u8` and `y: u8`, this is equivalent to `(x * y) mod 256`. 

[^wrapping-mul]:
    `wrapping_mul()` is a stable method available directly on all integer types 
    (`u8`, `u16`, `u32`, etc.) without any imports or feature flags. While wrapping 
    arithmetic operations were [originally part of the unstable `std::intrinsics` module](https://doc.rust-lang.org/std/intrinsics/fn.wrapping_mul.html), they were stabilized and moved to be inherent methods on integer types, making them part of Rust's stable API.

Replacing the usual multiplication operator we used with `wrapping_mul()` 
in the `square` function would fix the panic issue:
```{.rust .playable}
fn square(x: u8) -> u8 {
    x.wrapping_mul(x)
}
```

Observe, however, that `square(16)`, which is `16 * 16 = 256`, with `wrapping_mul()` returns zero! 
The function is **mathematically incorrect** for inputs > 15, 
even though it *doesn't technically panic*.

Wrapping arithmetic *is useful in many instances* where high-assurance code would be relevant, 
such as hash functions (where overflows are expected), cryptography (where modular arithmetic 
is intentional), and performance-critical code that aims to avoid overflow checks.

But specifically for `square`, it's **semantically** wrong: this is not what one 
would mathematically expect from the `square` function.

Thus, we conclude that the main problem is our `square` function only being well-defined when
its input is within `0` and `15`. Let's fix that!

### Solution A: Reflect the "partialness" of the function in Rust
The first solution to this issue is to take advantage of the built-in Rust `Option<T>` type, 
and make `square` return an `Option<u8>` instead of a standalone `u8`:
``` {.rust .playable}
fn square_option(x: u8) -> Option<u8> {
    if x >= 16 {
        None
    } else {
        Some(x * x)
    }
}
```

> **Remark on `Option<T>`**[^option-type]
>
> `Option<T>` is Rust's way of encoding **partial functions**[^partial-fn]. Instead of panicking on invalid inputs,
> the function returns `None`, making the "partiality" **explicit in the type signature**.
> Rust also provides convenient combinators like `.map()`, `.and_then()`, etc.

[^option-type]:
    The type [`Option`](https://doc.rust-lang.org/std/option/) represents an optional value: every `Option` is either 
    `Some` and contains a value, or `None`, and does not.

[^partial-fn]: 
    A **partial function** is one which may be undefined for some inputs, as opposed to a **total function** which is defined for all possible inputs in its domain. 
    
    For a mathematical treatment of total and partial functions, see: 
    Christopher Hollings (2014). [*Mathematics across the Iron Curtain: A History 
    of the Algebraic Theory of Semigroups*](https://books.google.com/books?id=O9wJBAAAQBAJ&pg=PA233). American Mathematical Society. p. 233. ISBN 978-1-4704-1493-1.

Here, F\* **is** able to prove panic-freedom: calling `square` with any
input is safe. Though, one could argue that `square` function's input being small
enough should *really* be an assumption, because in many algorithms we know upfront 
what valid input ranges are, and propagating `Option<T>` types throughout the codebase 
just to handle this boundary case creates **unnecessary complexity**. Having to deal with 
the possible integer overflow whenever you square a number is a huge burden. Can we do better?

### Solution B: Add a Pre-condition
Rust's type system doesn't directly allow the programmer to formalize the
assumption that `square` expects a small `u8`. However, this becomes
possible using hax: one can simply "annotate" a function with a **pre-condition
on its inputs**!

The pre-conditions and post-conditions on a function form a
**contract**: 
> _If you give me some inputs that satisfies a given formula_
(the "pre-condition"), _I will produce a return value that satisfy
another formula_ (the "postcondition")".

*Outside this contract*, (for all we know) anything can happen: the function might panic, 
it might run forever, erase your entire hard drive, etc.

The helper crate [hax-lib](https://github.com/cryspen/hax/tree/main/hax-lib)
provides the `hax_lib::requires(...)`
[procedural macro (proc-macro)](https://doc.rust-lang.org/reference/procedural-macros.html), 
which allows users to **directly write** hax pre-conditions in Rust: 
```{.rust .playable}
#[hax_lib::requires(x < 16)]
fn square_requires(x: u8) -> u8 {
    x * x
}
```

With this pre-condition, F\* **is** able to prove panic freedom! From now
on, it is the *responsibility* of the **"clients"** of the `square` function to **respect the defined
contract**. Thus, the next step is to verify that `square` is used correctly at every call site.

## Common panicking situations
Multiplication is not the only "panicking function" provided by the Rust standard
library: *most other integer arithmetic operations* can also panic due to overflow, and naturally also 
have similar informal assumptions about input bounds.

For instance, a different common source of panics is **indexing**. Indexing in an [array](https://doc.rust-lang.org/book/ch03-02-data-types.html#the-array-type), a [slice](https://doc.rust-lang.org/book/ch04-03-slices.html) or
a [vector](https://doc.rust-lang.org/book/ch08-01-vectors.html#storing-lists-of-values-with-vectors) is a **partial operation**[^partial-fn]: the index might simply be out of range.

In hax's `examples` directory (specifically `/examples/chacha20/`), you can find [an example 
implementation of `ChaCha20`](https://github.com/cryspen/hax/blob/main/examples/chacha20/src/lib.rs)
that makes use of pre-conditions to prove panic freedom in your code. We'll examine this example 
later in this chapter, showing how explicit pre-conditions can guarantee safe array access.

However, as we'll discover, explicit pre-conditions can become verbose when dealing with multiple parameters that need bounds checking. Another solution for safe indexing uses the **newtype pattern** combined with **refinement types** for *verification*. A newtype **wraps a primitive type** (like `usize`) in a **single-field struct** to create a distinct type with its own semantics—popularized in Rust through [matklad's blog post](https://matklad.github.io/2018/06/04/newtype-index-pattern.html). Combined with hax's *refinement annotations*, newtypes encode bounds constraints directly in types, eliminating explicit pre-conditions on every function. The [Data Invariants chapter](data-invariants.md#newtype-and-refinement-types) explores this in detail, showing how types like `StateIdx` guarantee compile-time index safety.

## Simple Example: Render Text with Pre-conditions

Here's a simple example that demonstrates the principles we have seen so far:
```{.rust .playable}
#[hax_lib::requires(message.len() <= 80)]
pub fn render_message(message: &[char]) -> [char; 80] {
    let mut display: [char; 80] = [' '; 80];
    assert!(80 >= message.len());  // ✓ Provable from pre-condition
    
    for i in 0..message.len() {
        display[i] = message[i];
    }
    display
}
```

This example models a classic 80-column text display (like old terminal screens or receipt printers) where you need to copy a message into a fixed-width display buffer. The pre-condition on `render_message` guarantees that the message fits within the 80-character limit, which in turn proves that the assertion in `copy_into_display` will never fail.

## Example: Proving Panic Freedom in ChaCha20

To illustrate how pre-conditions prove panic-freedom in real-world cryptographic code, 
we'll examine the **ChaCha20[^chacha20] example implementation from hax's examples directory** 
([`/examples/chacha20/`](https://github.com/cryspen/hax/tree/main/examples/chacha20)). 
This is an actual working example provided by the hax project to demonstrate these techniques.

[^chacha20]:
  **ChaCha20** is a high-speed stream cipher designed by Daniel J. Bernstein as a 
  variant of the Salsa20 cipher. It's widely used in modern cryptography, notably 
  in TLS 1.3, WireGuard VPN, and SSH, due to its combination of strong security 
  properties and efficient software implementation. ChaCha20 processes data in 
  64-byte blocks using a 256-bit key and operates through a series of quarter-round 
  functions that mix state through addition, XOR, and rotation operations.
  Reference: Bernstein, Daniel J. (2008). "ChaCha, a variant of Salsa20." 
  [https://cr.yp.to/chacha.html](https://cr.yp.to/chacha.html)

### The Index Out-of-Bounds Problem

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

This function could panic if `val.len() > 64`! In fact, the `assert!` check catches this at runtime, 
but F\* needs *static* proof that the assertion will never fail.

[^pub-super]:
    In the actual hax ChaCha20 implementation, this function is declared as 
    `pub(super) fn update_array(...)`, where `pub(super)` means "visible to the 
    parent module only." However, playground snippets run as top-level code without 
    a module hierarchy, so `pub(super)` would cause a compilation error 
    ("too many leading `super` keywords"). In these tutorial examples, we use 
    `fn` (private function) instead, which behaves identically for demonstration 
    purposes.

What `update_array(mut array: [u8; 64], val: &[u8]) -> [u8; 64]` does is precisely the following: 

- Takes a 64-byte array (note: `mut array` not `&mut`)
- Takes a borrowed slice of bytes (`val: &[u8]`) of any length
- Most importantly, it asserts `val` isn't longer than 64 bytes (**and PANICS if it is!**)
- Copies bytes from `val` into the beginning of `array`
- Leaves the rest of `array` unchanged (keeps original values past `val.len()`)
- Returns the modified `array`

### Using Pre-conditions to Prove Safety

Consider below how we use explicit pre-conditions in the ChaCha20 encryption function to guarantee safe array access 
(from `/examples/chacha20/src/lib.rs`):
```{.rust .playable}
# use hax_lib as hax;
# use hax_lib::RefineAs;
# type State = [u32; 16];
# type Block = [u8; 64];
# type ChaChaIV = [u8; 12];
# type ChaChaKey = [u8; 32];
# type StateIdx = hax_bounded_integers::BoundedUsize<0, 15>;
# #[hax::requires(bytes.len() >= 12)]
# fn to_le_u32s_3(bytes: &[u8]) -> [u32; 3] {
#     let mut out = [0; 3];
#     for i in 0..3 {
#         out[i] = u32::from_le_bytes(bytes[4 * i..4 * i + 4].try_into().unwrap());
#     }
#     out
# }
# #[hax::requires(bytes.len() >= 32)]
# fn to_le_u32s_8(bytes: &[u8]) -> [u32; 8] {
#     let mut out = [0; 8];
#     for i in 0..8 {
#         out[i] = u32::from_le_bytes(bytes[4 * i..4 * i + 4].try_into().unwrap());
#     }
#     out
# }
# #[hax::requires(bytes.len() >= 64)]
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
# fn chacha20_line(a: StateIdx, b: StateIdx, d: StateIdx, s: u32, m: State) -> State {
#     let mut state = m;
#     state[a] = state[a].wrapping_add(state[b]);
#     state[d] = state[d] ^ state[a];
#     state[d] = state[d].rotate_left(s);
#     state
# }
# fn chacha20_quarter_round(
#     a: StateIdx,
#     b: StateIdx,
#     c: StateIdx,
#     d: StateIdx,
#     state: State,
# ) -> State {
#     let state = chacha20_line(a, b, d, 16, state);
#     let state = chacha20_line(c, d, b, 12, state);
#     let state = chacha20_line(a, b, d, 8, state);
#     chacha20_line(c, d, b, 7, state)
# }
# fn chacha20_double_round(state: State) -> State {
#     let state = chacha20_quarter_round(
#         (0 as usize).into_checked(),
#         (4 as usize).into_checked(),
#         (8 as usize).into_checked(),
#         (12 as usize).into_checked(),
#         state,
#     );
#     let state = chacha20_quarter_round(
#         (1 as usize).into_checked(),
#         (5 as usize).into_checked(),
#         (9 as usize).into_checked(),
#         (13 as usize).into_checked(),
#         state,
#     );
#     let state = chacha20_quarter_round(
#         (2 as usize).into_checked(),
#         (6 as usize).into_checked(),
#         (10 as usize).into_checked(),
#         (14 as usize).into_checked(),
#         state,
#     );
#     let state = chacha20_quarter_round(
#         (3 as usize).into_checked(),
#         (7 as usize).into_checked(),
#         (11 as usize).into_checked(),
#         (15 as usize).into_checked(),
#         state,
#     );
#     let state = chacha20_quarter_round(
#         (0 as usize).into_checked(),
#         (5 as usize).into_checked(),
#         (10 as usize).into_checked(),
#         (15 as usize).into_checked(),
#         state,
#     );
#     let state = chacha20_quarter_round(
#         (1 as usize).into_checked(),
#         (6 as usize).into_checked(),
#         (11 as usize).into_checked(),
#         (12 as usize).into_checked(),
#         state,
#     );
#     let state = chacha20_quarter_round(
#         (2 as usize).into_checked(),
#         (7 as usize).into_checked(),
#         (8 as usize).into_checked(),
#         (13 as usize).into_checked(),
#         state,
#     );
#     chacha20_quarter_round(
#         (3 as usize).into_checked(),
#         (4 as usize).into_checked(),
#         (9 as usize).into_checked(),
#         (14 as usize).into_checked(),
#         state,
#     )
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
# fn chacha20_init(key: &ChaChaKey, iv: &ChaChaIV, ctr: u32) -> State {
#     let key_u32: [u32; 8] = to_le_u32s_8(key);
#     let iv_u32: [u32; 3] = to_le_u32s_3(iv);
#     [
#         0x6170_7865,
#         0x3320_646e,
#         0x7962_2d32,
#         0x6b20_6574,
#         key_u32[0],
#         key_u32[1],
#         key_u32[2],
#         key_u32[3],
#         key_u32[4],
#         key_u32[5],
#         key_u32[6],
#         key_u32[7],
#         ctr,
#         iv_u32[0],
#         iv_u32[1],
#         iv_u32[2],
#     ]
# }
# fn chacha20_encrypt_block(st0: State, ctr: u32, plain: &Block) -> Block {
#     let st = chacha20_core(ctr, st0);
#     let pl: State = to_le_u32s_16(plain);
#     let encrypted = xor_state(st, pl);
#     u32s_to_le_bytes(&encrypted)
# }
// The helper with precondition and assertion
#[hax::requires(val.len() <= 64)]
fn update_array(mut array: [u8; 64], val: &[u8]) -> [u8; 64] {
    assert!(64 >= val.len());
    for i in 0..val.len() {
        array[i] = val[i];
    }
    array
}

// The caller with matching precondition
#[hax::requires(plain.len() <= 64)]
pub fn chacha20_encrypt_last(st0: State, ctr: u32, plain: &[u8]) -> Vec<u8> {
    let mut b: Block = [0; 64];
    b = update_array(b, plain); // Note: This would panic if plain.len() > 64
    b = chacha20_encrypt_block(st0, ctr, &b);
    b[0..plain.len()].to_vec()
}
```

> **Note**: The code snippet above includes many helper functions that `chacha20_encrypt_last` depends on, don't be intimidated by the length! It's slightly modified from `/examples/chacha20/` for playground compatibility and, like the original example implementation, (internally) uses "refinement types" (covered in the ["Data Invariants" chapter](data-invariants.md)). 
> 
> Focus on the key pattern: `update_array` (*helper with assertion*) and `chacha20_encrypt_last` (*caller with pre-condition*).

Thus, the explicit pre-condition `#[hax::requires(plain.len() <= 64)]` in the encryption function above statically proves (in F\*) that the `assert!(64 >= val.len())` in the `update_array(...)` helper function will never fail.

**This successfully achieves panic-freedom! ✓**

### The Verbosity Problem

While explicit pre-conditions work, they can become verbose in practice. Notice how we had to write `#[hax_lib::requires(plain.len() <= 64)]` explicitly. For *functions with multiple parameters that need bounds checking*, this approach quickly becomes **unwieldy**.

Consider a hypothetical function that operates on ChaCha20's 16-element state array:
```{.rust .playable}
# type State = [u32; 16];
#[hax_lib::requires(i0 < 16 && i1 < 16 && i2 < 16 && i3 < 16)]
fn quarter_round_verbose(i0: usize, i1: usize, i2: usize, i3: usize, state: State) -> State {
    state // Simplified (for illustration purposes)
}
```

Every function that takes indices would need similar annotations! This is error-prone and clutters the code. In the ["Data Invariants" chapter](data-invariants.md), we'll see how **refinement types** can encode these constraints directly in the type system, eliminating the need for repetitive pre-conditions.


## Assumptions: A Verification Helper

Beyond pre-conditions, there's one more tool you might encounter when working with hax: **assumptions**.

### What are `hax_lib::assume!` statements?

These are NOT pre-conditions! They're **hints to help F\* understand intermediate facts** during verification. Unlike pre-conditions (*which create obligations for callers*) or refinement types (*which enforce invariants through the type system*), assumptions simply tell F\* "*trust me, this fact is true here*."

> **Summary:**
> 
> - **Pre-conditions** (`#[requires(...)]`): contracts that *callers* must prove. 
> - **Refinement types** (covered in the ["Data Invariants" chapter](data-invariants.md)): invariants that *types* guarantee. 
> - **Assumptions** (`hax_lib::assume!(...)`): facts that *you assert* to help F\*.

### Example: Loop Invariants in ChaCha20

Consider the current implementation of the `chacha20_update` function (from `/examples/chacha20/src/lib.rs`):
```rust
pub fn chacha20_update(st0: State, m: &[u8]) -> Vec<u8> {
    let mut blocks_out = Vec::new();
    let num_blocks = m.len() / 64;
    let remainder_len = m.len() % 64;
    for i in 0..num_blocks {
        // Full block
        let b =
            chacha20_encrypt_block(st0, i as u32, &m[64 * i..(64 * i + 64)].try_into().unwrap());
        hax_lib::assume!(blocks_out.len() == i * 64); // Helps F* track the loop invariant
        blocks_out.extend_from_slice(&b);
    }
    hax_lib::assume!(blocks_out.len() == num_blocks * 64); // Asserts what we know after the loop
    if remainder_len != 0 {
        // Last block
        let b = chacha20_encrypt_last(st0, num_blocks as u32, &m[64 * num_blocks..m.len()]);
        blocks_out.extend_from_slice(&b);
    }
    blocks_out
}
```

*Here*, the **assumptions help F\* understand that the vector length grows predictably**: after each iteration `i`, the length is exactly `i * 64` bytes. Without these hints, F\* might not be able to prove that subsequent operations are safe at all, *even though* we (as programmers) know the invariant holds.

> **CAUTION: Use with extreme care!** An incorrect assumption can make F\* verify unsound code. 
> Unlike pre-conditions (which *shift the burden of proof to callers*) and [refinement types](data-invariants.md) 
> (which are *enforced by the type system*), **assumptions are taken on faith**. If you assume 
> something false, you've broken the verification guarantees!

### A Better Approach: Verified Loop Invariants

While `hax_lib::assume!` statements **work** for tracking loop properties, they represent a verification gap: *we're asking F\* to trust these facts without proof*. A far better approach is to use **proper loop invariants** that F\* can actually verify. Hax provides the `hax_lib::loop_invariant!` macro for this purpose: instead of blindly trusting our claims, F\* proves that the invariant holds through mathematical induction. 

Here's the same `chacha20_update` function rewritten with a verified loop invariant:
```{.rust .playable}
# // #![feature(stmt_expr_attributes)]
# use hax_lib as hax;
# use hax_lib::RefineAs;
# type State = [u32; 16];
# type Block = [u8; 64];
# type StateIdx = hax_bounded_integers::BoundedUsize<0, 15>;
# // Note: Removed `to_le_u32s_3`, `to_le_u32s_8`, `chacha20_init`, `chacha20_key_block`,
# // and `chacha20_key_block0` for simplicity, as they aren't called by `chacha20_update`.
# #[hax::requires(bytes.len() >= 64)]
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
# #[hax::requires(val.len() <= 64)]
# fn update_array(mut array: [u8; 64], val: &[u8]) -> [u8; 64] {
#     assert!(64 >= val.len());
#     for i in 0..val.len() {
#         array[i] = val[i];
#     }
#     array
# }
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
#     let state = chacha20_quarter_round((0 as usize).into_checked(), (4 as usize).into_checked(), (8 as usize).into_checked(), (12 as usize).into_checked(), state);
#     let state = chacha20_quarter_round((1 as usize).into_checked(), (5 as usize).into_checked(), (9 as usize).into_checked(), (13 as usize).into_checked(), state);
#     let state = chacha20_quarter_round((2 as usize).into_checked(), (6 as usize).into_checked(), (10 as usize).into_checked(), (14 as usize).into_checked(), state);
#     let state = chacha20_quarter_round((3 as usize).into_checked(), (7 as usize).into_checked(), (11 as usize).into_checked(), (15 as usize).into_checked(), state);
#     let state = chacha20_quarter_round((0 as usize).into_checked(), (5 as usize).into_checked(), (10 as usize).into_checked(), (15 as usize).into_checked(), state);
#     let state = chacha20_quarter_round((1 as usize).into_checked(), (6 as usize).into_checked(), (11 as usize).into_checked(), (12 as usize).into_checked(), state);
#     let state = chacha20_quarter_round((2 as usize).into_checked(), (7 as usize).into_checked(), (8 as usize).into_checked(), (13 as usize).into_checked(), state);
#     chacha20_quarter_round((3 as usize).into_checked(), (4 as usize).into_checked(), (9 as usize).into_checked(), (14 as usize).into_checked(), state)
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
# #[hax::requires(plain.len() <= 64)]
# fn chacha20_encrypt_last(st0: State, ctr: u32, plain: &[u8]) -> Vec<u8> {
#     let mut b: Block = [0; 64];
#     b = update_array(b, plain);
#     b = chacha20_encrypt_block(st0, ctr, &b);
#     b[0..plain.len()].to_vec()
# }
pub fn chacha20_update(st0: State, m: &[u8]) -> Vec<u8> {
    let mut blocks_out = Vec::new();
    let num_blocks = m.len() / 64;
    let remainder_len = m.len() % 64;
    for i in 0..num_blocks {
        // Note that this is a for loop, meaning that loop_invariant!() takes a closure here
        hax_lib::loop_invariant!(|i: usize| blocks_out.len() == i * 64);
        let b = chacha20_encrypt_block(st0, i as u32, &m[64 * i..(64 * i + 64)].try_into().unwrap());
        blocks_out.extend_from_slice(&b);
    }
    if remainder_len != 0 {
        let b = chacha20_encrypt_last(st0, num_blocks as u32, &m[64 * num_blocks..m.len()]);
        blocks_out.extend_from_slice(&b);
    }
    blocks_out
}
```

**Why is this better?**

| Approach | Safety | Maintainability | Risk |
|----------|--------|----------------|------|
| **`assume!` statements** | Trusted, not verified | Brittle (easy to get wrong) | High (false assumptions break soundness) |
| **`loop_invariant!` statements** | Actually verified by F\* | Self-documenting | Low (F\* proves them correct) |

With `#[hax_lib::loop_invariant!(...)]`, F\* proves that:

1. The invariant holds *before the loop starts* (**base case**)
2. If it holds at the *start of iteration* `i`, it still holds *at the end* (**inductive step**)
3. After the loop *completes*, we can rely on the invariant being true (**conclusion**)

This verification follows the principle of **mathematical induction**: just as induction proves properties for all natural numbers, *loop invariants prove properties across all loop iterations*. This gives us mathematical certainty rather than blind trust. The code is clearer too, since the loop invariant explicitly states what property we're maintaining throughout the iteration.

> **Best Practice**: *Use loop invariants instead of assumptions whenever possible*. Reserve `assume!` for cases where F\* needs temporary hints during development, and always replace them with *proper* specifications **before production use**.

> **IMPORTANT: Loop Invariant Syntax**
>
> Loop annotations (such as `loop_invariant!` and `loop_decreases!`) must appear **first** in the loop body, before *any other statements*:
>
> - **For `for` loops**: Use a **closure** that *captures the loop variable*:
>   ```rust
>   for i in 0..n {
>       hax_lib::loop_invariant!(|i: usize| property_holds(i));
>       // ... rest of loop body
>   }
>   ```
>
> - **For `while` loops**: Use an **expression** directly:
>   ```rust
>   while condition {
>       hax_lib::loop_decreases!(measure);
>       hax_lib::loop_invariant!(property_holds);
>       // ... rest of loop body
>   }
>   ```
>
> The loop variable in the closure parameter (`|i: usize|`) **shadows** the *actual* loop variable, allowing F\* to *reason about the invariant at any iteration*.

## What's Next?

We've seen how explicit pre-conditions can prove panic freedom, but the approach has limitations:

1. **Verbose**: *Every* function needs explicit annotations
2. **Error-prone**: Easy to forget a pre-condition
3. **Repetitive**: Similar bounds checks appear *everywhere*

The ["Data Invariants" chapter](data-invariants.md) shows a more elegant solution: **encoding pre-conditions directly in types** using refinement types. We'll revisit the ChaCha20 example to see how this dramatically simplifies verification!

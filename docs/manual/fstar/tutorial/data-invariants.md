---
weight: 2
---

# Data invariants

In the two previous chapters we saw how to write specifications on
functions, be it with pre-conditions, post-conditions, or with lemmas. In this
chapter, we will see how to maintain invariants with precise types.

## Making illegal states unpresentable
With the Barrett example, we were working with a certain field, whose
elements were represented as `i32` integers. To simplify, let's
consider `F₃`, the finite field[^field-def] with 3 elements (say `0`, `1` and `2`).

[^field-def]: 
    A **finite field** (or **Galois field**) is a field with finitely many elements 
    satisfying the field axioms: closure under addition, multiplication, subtraction, 
    and division (except by zero). The simplest examples are `Fₚ = {0, 1, ..., p-1}`
    for prime `p`, where arithmetic is performed modulo `p`. For instance, in `F₃ = {0, 1, 2}`, 
    we have `2 + 2 = 1` (since `4 mod 3 = 1`) and `2 × 2 = 1`. Computing with elements of `Fₚ` 
    means ordinary arithmetic of integers with reduction modulo `p`."
    
    Reference: Lidl, Rudolf; Niederreiter, Harald (2008). *Finite Fields* (2nd ed.). 
    Cambridge University Press. p. 15, Definition 1.41. ISBN 978-0-521-06567-2.

Representing `F₃` elements as `i32`s creates a problem[^i32-representation]: every 
function consuming `F₃` elements risks accepting *illegal* values. We're back to 
the ["Panic Freedom" chapter](panic-freedom.md): requiring panics and hax pre-conditions on every 
function. That's not optimal: the property of being `0`, `1`, or `2` should be 
**encoded directly in the type** representing `F₃` elements.

[^i32-representation]:
    While every `F₃` element `{0, 1, 2}` fits in an `i32` (range: −2³¹ to 2³¹ − 1), 
    the vast majority of `i32` values are not valid `F₃` elements. This asymmetry 
    forces runtime validation.

### `enum`s to the rescue!
Rust alone already can solve our representation issues with
[enums](https://doc.rust-lang.org/book/ch06-00-enums.html)! That is, 
where `struct` give you a way of grouping together related fields and 
data, like a `Rectangle` with its `width` and `height`, `enum` give you 
a way of saying a value is one of a possible set of values. You are 
effectively encoding program state in the type system itself. 

Below, we define the `enum` type `F3` which has only three constructors: 
`F3` represent exactly the elements of `F₃`, not more, not less.

```{.rust .playable}
enum F3 {
    Zero,
    One,
    Two,
}
```

Let's see this in action with a total function that does something more concrete:
```{.rust .playable}
# enum F3 {
#     Zero,
#     One,
#     Two,
# }
fn f3_add(a: F3, b: F3) -> F3 {
    match (a, b) {
        (F3::Zero, x) | (x, F3::Zero) => x,
        (F3::One, F3::One) => F3::Two,
        (F3::One, F3::Two) | (F3::Two, F3::One) => F3::Zero,
        (F3::Two, F3::Two) => F3::One,
    }
}
```

Notice something crucial: **we don't need a default case** (the `_` pattern). 
Rust's exhaustiveness checker **guarantees at compile-time** that we've handled every possible 
combination, i.e. that any value of type `F3` can only be one of these three constructors. 
This function is **total**[^total-fn], and thus can never panic. We completely dropped a source of panic!

[^total-fn]: 
    A **total function** is one that is defined for all possible inputs in its domain, 
    as opposed to a partial function which may be undefined for some inputs. 
    
    For a mathematical treatment of total and partial functions, see: 
    Christopher Hollings (2014). [*Mathematics across the Iron Curtain: A History 
    of the Algebraic Theory of Semigroups*](https://books.google.com/books?id=O9wJBAAAQBAJ&pg=PA233). American Mathematical Society. p. 233. 
    ISBN 978-1-4704-1493-1.

Rust's **type system** is helpful here in that it allows us to fundamentally 
rule out the existence of "invalid" `F3` values in safe Rust: 

- *Theoretically*, `enum`s are closed algebraic data types (ADTs): all possible values are exhaustively defined by the declared variants.
- *Practically*, every `F3` value must be constructed through `Zero`, `One`, or `Two`, i.e. there's no mechanism to forge values or manipulate bit patterns outside these constructors.

With the `enum` we defined, only 3 values can exist: illegal states are 
unrepresentable.[^enum-vs-i32] This has profound implications: **no runtime 
checks** are needed, **no panics** are possible, and all functions operating on 
`F3` are **total**.

[^enum-vs-i32]:
    **Contrast this with `i32`**: any value from −2³¹ to 2³¹ − 1 can be created, but only 
    3 are valid F₃ elements. 
    
    Every function must then validate inputs with runtime 
    checks, like `if value > 2 { panic!(...) }`.

However, soon you'd want to work with a bigger finite field, like `F₂₃₄₇`. While this works 
beautifully for `F₃`, it breaks down for larger fields, since 2347 `enum` variants would be 
impractical!

### `Newtype` and Refinement Types
Since we wouldn't want to work with a 2347-element `enum`, we have to revert to
a type that can comfortably hold this many elements. The smallest Rust 
integer type that is large enough for our needs is `u16`.

Let's define `F` as a
[`newtype`](https://matklad.github.io/2018/06/04/newtype-index-pattern.html), i.e. 
a [struct](https://doc.rust-lang.org/book/ch05-00-structs.html) with
one `u16` field `v`. 

The **`newtype` pattern** is a widely-used Rust idiom where you wrap an existing type in a single-field `struct` to create a distinct type with its own semantics. Originally from Haskell and popularized in the Rust community through blog posts like [matklad's "Newtype Index Pattern"](https://matklad.github.io/2018/06/04/newtype-index-pattern.html), newtypes provide compile-time type safety at zero runtime cost. For example, wrapping `usize` in `struct UserId(usize)` prevents accidentally using a user ID where a post ID is expected, even though both are represented identically in memory. In our case, we'll use a newtype not just for type safety, but to attach a **refinement** that constrains the valid range of values.

Notice the refinement annotation on `v`: the
extraction of this type `F` via hax will result in a type enforcing
`v` to be small enough for our needs.

``` {.rust .playable}
pub const Q: u16 = 2347;

#[hax_lib::attributes]
pub struct F {
    #[hax_lib::refine(v < Q)]
    pub v: u16,
}
```

> **Why `#[hax_lib::attributes]`?** 
>
> This marker tells hax to process refinement attributes (`#[refine(...)]`) 
> on the fields inside this struct. 
> Without it, hax would ignore the refinement and treat `v` as a plain `u16`.

In Rust, we can now define functions that operate on type `F`,
assuming they are in bounds with respect to `F₂₃₄₇`: every such
assumption will be checked and enforced by the proof assistant. 

As an example, below is an implementation of the addition operation for the `F` type:

``` {.rust .playable}
# pub const Q: u16 = 2347;
# #[hax_lib::attributes]
# pub struct F {
#     #[hax_lib::refine(v < Q)]
#     pub v: u16,
# }
use core::ops::Add;

impl Add for F {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self {
            v: (self.v + rhs.v) % Q,
        }
    }
}
```

### Creating Field Elements

When constructing `F` values from raw `u16` integers, we have two options:

**Option 1: Panic on invalid input** (use when caller should guarantee validity):
``` {.rust .playable}
# use core::ops::Add;
# pub const Q: u16 = 2347;
# #[hax_lib::attributes]
# pub struct F {
#   #[hax_lib::refine(v < Q)]
#    pub v: u16,
# }
# impl Add for F {
#     type Output = Self;
#     fn add(self, rhs: Self) -> Self {
#        Self {
#            v: (self.v + rhs.v) % Q,
#        }
#    }
# }
#[hax_lib::requires(value < Q)]
pub fn new(value: u16) -> Self {
    assert!(value < Q);
    Self { v: value }
}
```

**Option 2: Return `Option` for fallible construction** (use when input might be invalid):
``` {.rust .playable}
# use core::ops::Add;
# pub const Q: u16 = 2347;
# #[hax_lib::attributes]
# pub struct F {
#   #[hax_lib::refine(v < Q)]
#    pub v: u16,
# }
# impl Add for F {
#     type Output = Self;
#     fn add(self, rhs: Self) -> Self {
#        Self {
#            v: (self.v + rhs.v) % Q,
#        }
#    }
# }
pub fn try_new(value: u16) -> Option<Self> {
    if value < Q {
        Some(Self { v: value })
    } else {
        None
    }
}
```

Notice that even `new` requires the pre-condition `#[hax_lib::requires(value < Q)]`, even though `assert!` provides a runtime check. Formal verification demands explicit contracts that can be proven statically, **not just runtime assertions**.

Here, when hax extracts this code to F\*, the proof assistant is able 
to automatically prove that:

1. The addition operation doesn't overflow, 
i.e. `(self.v + rhs.v)` doesn't exceed `u16::MAX` (2¹⁶ − 1)
    - F\* knows: `self.v < 2347` and `rhs.v < 2347`
    - *Therefore*: `self.v + rhs.v < 4694 < 65536`
    - **Verified! ✓**


2. The invariant of `F` is preserved, 
i.e. `(self.v + rhs.v) % Q < Q` holds
    - F\* proves the modulo operation always returns values `[0, Q)` 
    - **Verified! ✓**

Notice that the definition of the `F` type in F\* (named `t_F`) 
very explicitly requires the invariant as a refinement on `v`.
   
These proofs happen completely **automatically**, no manual proof required!

## Revisiting ChaCha20: Refinement Types in Action

In one of the previous chapters, ["Panic Freedom"](panic-freedom.md), we saw how explicit pre-conditions like `#[hax_lib::requires(plain.len() <= 64)]` can prove that array operations don't panic. However, we also noted that this approach becomes verbose when dealing with multiple parameters that need bounds checking.

Let's revisit the ChaCha20 example to see how **refinement types** provide a more elegant solution by encoding pre-conditions directly in the type system.

### The Problem with Explicit Pre-conditions

Recall that ChaCha20 operates on a 16-element state array of `u32` values:
```rust
type State = [u32; 16];
```

Any function that operates on specific indices of this array needs to ensure the indices are in bounds (`0..16`). With explicit pre-conditions, every such function requires repetitive annotations:

```{.rust .playable}
# type State = [u32; 16];
#[hax_lib::requires(i0 < 16 && i1 < 16 && i2 < 16 && i3 < 16)]
fn quarter_round_verbose(i0: usize, i1: usize, i2: usize, i3: usize, state: State) -> State {
    state // Simplified (for illustration purposes)
}
```

This is very tedious, error-prone, and clutters the code. Every function accepting indices would need similar bounds checks!

### The Solution: Refinement Types (Implicit Pre-conditions)

Not all pre-conditions require explicit `#[requires(...)]` annotations, they can be encoded directly in the type system! That is, instead of annotating every function, we can define a **refinement type** for state indices that encodes the bounds constraint once (from `/examples/chacha20/src/lib.rs`): 
```{.rust .playable}
# use hax_bounded_integers;
type StateIdx = hax_bounded_integers::BoundedUsize<0, 15>;
```

This type represents a `usize` value that is **guaranteed** to be in the range `[0, 15]`. The `hax_bounded_integers` crate provides this bounded integer type that hax extracts with the appropriate refinement.

Notice that every use of `StateIdx` (from `/examples/chacha20/src/lib.rs`) is associated with this implicit pre-condition. This means that now any function accepting `StateIdx` automatically gets the bounds guarantee without explicit annotations: 
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

**No pre-conditions needed!** F\* can prove that all array accesses are safe because the type system guarantees that `a`, `b`, and `d` are valid indices.

### Comparing the Two Approaches

Let's directly compare the explicit pre-condition approach from the ["Panic Freedom" chapter](panic-freedom.md) with the refinement type approach:

| Aspect | Explicit Pre-conditions | Refinement Types |
|--------|------------------------|------------------|
| **Definition** | Per-function annotations | Single type definition |
| **Example** | `#[requires(i < 16)] fn f(i: usize)` | `fn f(i: StateIdx)` |
| **Verbosity** | High (repeated for every function) | Low (type carries the invariant) |
| **Maintenance** | Error-prone (easy to forget) | Compiler-enforced |
| **Call sites** | Must prove pre-condition | Type checking suffices |
| **Conceptual model** | Properties about *functions* | Properties about *data* |

**Main takeaway**: We shifted from proving properties about *functions* (via pre-conditions) to proving properties about *data* (via types). This is a fundamental change in how we think about verification!

### Using Refined Indices in Practice

Here's how we can use these refined indices we constructed in ChaCha20's quarter round function (from `/examples/chacha20/src/lib.rs`):

```{.rust .playable}
# use hax_bounded_integers;
# type State = [u32; 16];
# type StateIdx = hax_bounded_integers::BoundedUsize<0, 15>;
# fn chacha20_line(a: StateIdx, b: StateIdx, d: StateIdx, s: u32, m: State) -> State {
#     let mut state = m;
#     state[a] = state[a].wrapping_add(state[b]);
#     state[d] = state[d] ^ state[a];
#     state[d] = state[d].rotate_left(s);
#     state
# }
pub fn chacha20_quarter_round(
    a: StateIdx,
    b: StateIdx,
    c: StateIdx,
    d: StateIdx,
    state: State,
) -> State {
    let state = chacha20_line(a, b, d, 16, state);
    let state = chacha20_line(c, d, b, 12, state);
    let state = chacha20_line(a, b, d, 8, state);
    chacha20_line(c, d, b, 7, state)
}
```

Notice how clean this is! No `#[requires(...)]` annotations anywhere, yet F\* can verify that all operations are panic-free.

### Creating "Refined" Values

When we need to create `StateIdx` values from constants, we use the `.into_checked()` method (from `/examples/chacha20/src/lib.rs`):

```{.rust .playable}
# use hax_bounded_integers;
# use hax_lib::*;
# type State = [u32; 16];
# type StateIdx = hax_bounded_integers::BoundedUsize<0, 15>;
# fn chacha20_quarter_round(a: StateIdx, b: StateIdx, c: StateIdx, d: StateIdx, state: State) -> State {
#     state // Simplified (for illustration purposes)
# }
fn chacha20_double_round(state: State) -> State {
    let state = chacha20_quarter_round(
        0.into_checked(),   // ✓ 0 is provably in [0, 15]
        4.into_checked(),   // ✓ 4 is provably in [0, 15]
        8.into_checked(),   // ✓ 8 is provably in [0, 15]
        12.into_checked(),  // ✓ 12 is provably in [0, 15]
        state,
    );
    // ... more rounds
    state
}
```

The `.into_checked()` method converts a constant integer literal into a `StateIdx`, and F\* verifies at compile-time that the value is within bounds. If you tried `16.into_checked()`, verification would fail!

### Why Refinement Types Matter

Refinement types demonstrate one of the main principles of formal verification: **making illegal states unrepresentable**. 

With `StateIdx`:

- **Impossible to create** an out-of-bounds index in safe code  ✓
- **Guaranteed at the type level** that all indices are valid  ✓
- **No runtime overhead** after verification (types erase at runtime)  ✓
- **Zero pre-conditions** needed on functions using refined indices  ✓

This is the same principle we saw with the `F3` enum earlier, but applied to numeric ranges! While `enum`s work perfectly for small discrete sets, refinement types scale to handle bounded numeric types efficiently.

## Proof Approach Guide

Putting it all together, here's a guide on when to use each approach to ensure data invariants:

| Approach | Pros | Cons | Best used for... |
|----------|------|------|----------|
| **Enum** | Perfect type safety, exhaustive matching | Impractical for large sets | Small discrete domains (< 20 values) |
| **Refinement Types** | Scales to any size, precise verification | Requires a proof assistant | Bounded numeric types, indices |
| **Plain integers with preconditions** | No new types needed | Verbose, easy to forget checks | Quick prototypes, one-off validations |

The progression from `enum` to refinement types to explicit pre-conditions represents a necessary trade-off between **type safety** and **flexibility**:

- **Pre-conditions**: Minimum safety guarantees from types, maximum flexibility (any value, checked at function boundaries)
- **Refinement types**: High safety, good flexibility (constrained ranges)
- **Enums**: Maximum safety, minimum flexibility (fixed set of values)

Choose the strongest approach that fits your domain: encode invariants in types whenever possible!

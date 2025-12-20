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
[chapter 4.1](panic-freedom.md): requiring panics and hax pre-conditions on every 
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
    E1,
    E2,
    E3,
}
```

With `F3`, there doesn't exist illegal values at all: we can now
define *total functions*[^total-fn] on `F₃` elements. The Rust compiler 
**guarantees at compile-time** that any value of type `F3` can only be 
one of these three constructors. We dropped altogether a source of panic!

[^total-fn]: 
    A **total function** is one that is defined for all possible inputs in its domain, 
    as opposed to a partial function which may be undefined for some inputs. 
    
    For a mathematical treatment of total and partial functions, see: 
    Christopher Hollings (2014). [*Mathematics across the Iron Curtain: A History 
    of the Algebraic Theory of Semigroups*](https://books.google.com/books?id=O9wJBAAAQBAJ&pg=PA233). American Mathematical Society. p. 233. 
    ISBN 978-1-4704-1493-1.

Rust's type system is helpful here in that it allows us to fundamentally 
rule out the existence of "invalid" `F3` values in safe Rust, since 
the type system prevents this possibility entirely.

With the `enum`, only 3 values can exist, i.e. illegal states are unrepresentable.[^enum-vs-i32] 
No runtime checks needed, no panics possible, and all functions are total.

Soon you'd want to work with a bigger finite field like `F₂₃₄₇`. While this works 
beautifully for `F₃`, it breaks down for larger fields, since 2347 enum variants would be 
impractical!

[^enum-vs-i32]:
    **Contrast this with `i32`**: any value from −2³¹ to 2³¹ − 1 can be created, but only 
    3 are valid F₃ elements. 
    
    Every function must then validate inputs with runtime 
    checks, like `if value > 2 { panic!(...) }`.

### Newtype and Refinement Types
Since we wouldnt want to with a 2347-element `enum`, we have to revert to
a type that can comfortably hold this many elements. The smallest Rust 
integer type that is large enough for our needs is `u16`.

Let's define `F` a
["newtype"](https://matklad.github.io/2018/06/04/newtype-index-pattern.html):
a [struct](https://doc.rust-lang.org/book/ch05-00-structs.html) with
one `u16` field `v`. Notice the refinement annotation on `v`: the
extraction of this type `F` via hax will result in a type enforcing
`v` to be small enough.

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

As an example, below is an implementation of the addition operation for `F` type:

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

We can do more concrete things involving these constructors:
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

impl F {
    pub fn new(value: u16) -> Self {
        /// Create a new field element, & panicking if out of bounds
        assert!(value < Q);
        Self { v: value }
    } 

    pub fn try_new(value: u16) -> Option<Self> {
        /// Try to create a field element, & returning None if invalid
        if value < Q {
            Some(Self{v: value})
        } else {
            None
        }
    }
}
```

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

## Proof Approach Guide

| Approach | Pros | Cons | Best used for... |
|----------|------|------|----------|
| **Enum** | Perfect type safety, exhaustive matching | Impractical for large sets | Small domains (< 20 values) |
| **Refinement Types** | Scales to any size, precise verification | Requires proof assistant | Bounded numeric types |
| **Plain integers with preconditions** | No new types needed | Verbose, easy to forget checks | Quick prototypes |

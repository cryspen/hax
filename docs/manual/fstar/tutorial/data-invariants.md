---
weight: 2
---

# Data invariants

In the two previous chapters we saw how to write specifications on
functions, be it with pre and post-condition or with lemmas. In this
chapter, we will see how to maintain invariants with precise types.

## Making illegal states unpresentable
With the Barrett example, we were working on a certain field, whose
elements were represented as `i32` integers. To simplify, let's
consider `F₃`, the [finite field](https://en.wikipedia.org/wiki/Finite_field) with 3 elements (say `0`, `1` and
`2`). On a pedantic note, a finite field is a field that is a finite 
set; this means that it has a finite number of elements on which 
multiplication, addition, subtraction and division (excluding division 
by zero) are defined and satisfy the [field axioms](https://en.wikipedia.org/wiki/Field_axioms).

Every element of `F3` can be easily represented as a `i32` integer,
but it is easy to see that the converse doesn't hold: the vast 
majority of `i32` integers are not in of `F₃`.

If were representing `F₃` elements as `i32`s, everytime we define 
a function "consuming" `F₃` elements, we face the risk to "consume" 
*illegal* elements. We are thus back to [chapter 4.1](panic-freedom.md): 
we should panic on *illegal* elements, and add hax pre-conditions on 
every single function, just like before. That's not optimal: 
ideally, we would want the property of being either `0`, `1`, 
or `2` should be encoded directly in the type representing `F₃` elements.

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
define [*total*
functions](https://en.wikipedia.org/wiki/Partial_function) on `F₃`
elements. The Rust compiler **guarantees at compile-time** that any 
value of type `F3` can only be one of these three constructors. 
We dropped altogether a source of panic!

There is literally no way in safe Rust to construct an "invalid" `F3` 
value, since the type system prevents this possibility entirely.

**Contrast this with using `i32`:**
- Any `i32` value can be created (−2³¹ to 2³¹ − 1)
- Only 3 of those values are "valid" F₃ elements (say `0`, `1`, `2`)
- You need runtime checks: `if value > 2 { panic!(...) }`
- Functions must constantly validate their inputs

**With the `enum`:**
- Only 3 values can exist
- No runtime checks needed
- No panics possible from invalid values
- Functions are **total** (i.e. defined for all possible inputs of that type)

Soon you would want to work with a bigger finite field: say
`F₂₃₄₇`. While our first approach works beautifully for small sets (`F₃`), 
it breaks down for larger fields (`F₂₃₄₇` would need 2347 `enum` variants!). 
Clearly, representing this many `q` different elements with an Rust
enum would be very painful... The `enum` approach completely falls apart!

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
> This marker tells hax to process refinement attributes (`#[refine(...)]`) 
> on the fields inside this struct. Without it, hax would ignore the 
> refinement and treat `v` as a plain `u16`.

In Rust, we can now define functions that operate on type `F`,
assuming they are in bounds with respect to `F₂₃₄₇`: every such
assumption will be checked and enforced by the proof assistant. 

As an example, below is an implementation of the addition operation for `F` type:

``` {.rust .playable}
# pub const Q: u16 = 2347;
# 
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
        else {
            None
        }
        }
    }
}
```

Here, when hax extracts this code to F\*, the proof assistant is able 
to automatically prove that:

1. The addition operation doesn't overflow, 
i.e. `(self.v + rhs.v)` doesn't exceed `u16::MAX` (2¹⁶ − 1)
   - F\* knows: `self.v < 2347` and `rhs.v < 2347`
   - Therefore: `self.v + rhs.v < 4694 < 65536`
   - Verified! ✓

2. The invariant of `F` is preserved, 
i.e. `(self.v + rhs.v) % Q < Q` holds
   - F\* proves the modulo operation always returns values `[0, Q)` 
   - Verified! ✓

Notice that the definition of the `F` type in F\* (named `t_F`) 
very explicitly requires the invariant as a refinement on `v`.
   
These proofs happen completely **automatically**, no manual proof required!

## Proof Approach Guide

| Approach | Pros | Cons | Best used for... |
|----------|------|------|----------|
| **Enum** | Perfect type safety, exhaustive matching | Impractical for large sets | Small domains (< 20 values) |
| **Refinement Types** | Scales to any size, precise verification | Requires proof assistant | Bounded numeric types |
| **Plain integers with preconditions** | No new types needed | Verbose, easy to forget checks | Quick prototypes |

---
weight: 0
---

# Panic freedom

Let's start with a simple example: a function that squares a `u8`
integer. To extract this function to Lean using hax, we simply need to
run the command `cargo hax into lean` in the directory of the crate
in which the function `square` is defined.

*Note: throughout this tutorial, you can edit the snippets of code and
extract to Lean by clicking the play button (:material-play:), or even typecheck it with the button (:material-check:).*

```{.rust .playable .lean-backend}
fn square(x: u8) -> u8 {
    x * x
}
```

If we run `lake build` on the result (or type-check using the playground), we get a success. If you followed the F\* tutorial, this might be a surprise because the function is not 
panic-free. Indeed, our encoding of Rust code in Lean wraps everything in a result monad. And 
functions that panic return an error in this monad. To try to prove panic-freedom, we have to 
specify that the result of `square` is expected not to be an error in this result type. A way
to do that is the following:
```{.rust .playable .lean-backend .expect-failure}
#[hax_lib::requires(true)]
#[hax_lib::ensures(|res| true)]
fn square(x: u8) -> u8 {
    x * x
}
```
Adding a `hax_lib::requires` and a `hax_lib::ensures` annotation will make Hax generate a specification of the function, asserting panic freedom as well as the postcondition. Here, we used the trivial postcondition `true`, so we only assert panic freedom.

If we try running `lake build`
after extracting this code, we get an error: 
`The prover found a counterexample, consider the following assignment: value = 255`. Indeed `square(255)` 
panics because the multiplication overflows.

## Rust and panicking code
Quoting the chapter [To `panic!` or Not to
`panic!`](https://doc.rust-lang.org/book/ch09-03-to-panic-or-not-to-panic.html)
from the Rust book:

> The `panic!` macro signals that your program is in a state it can't
> handle and lets you tell the process to stop instead of trying to
> proceed with invalid or incorrect values.

A Rust program should panic only in a situation where an assumption
or an invariant is broken: a panic models an *invalid* state. Formal
verification is about proving such invalid state cannot occur, at all.

From this observation emerges the urge of proving Rust programs to be
panic-free!

## Fixing our squaring function
Let's come back to our example. There is an informal assumption to the
multiplication operator in Rust: the inputs should be small enough so
that the addition doesn't overflow.

Note that Rust also provides `wrapping_mul`, a non-panicking variant
of the multiplication on `u8` that wraps when the result is bigger
than `255`. Replacing the common multiplication with `wrapping_mul` in
`square` would fix the panic, but then, `square(256)` returns zero.
Semantically, this is not what one would expect from `square`.

Our problem is that our function `square` is well-defined only when
its input is within `0` and `15`.

### Solution: add a precondition

We already added a pre-condition to specify panic-freedom but we can turn it into a more interesting pre-condition to restrict the inputs and stay in the domain where the multiplication fits in a `u8`. We only need to modify the Rust condition that is passed to the `hax_lib::requires` macro: 

```{.rust .playable .lean-backend}
#[hax_lib::requires(x < 16)]
#[hax_lib::ensures(|res| true)]
fn square(x: u8) -> u8 {
    x * x
}
```

With this precondition, Lean is able to prove panic freedom. From now
on, it is the responsibility of the clients of `square` to respect the
contract.

## Common panicking situations
Multiplication is not the only panicking function provided by the Rust
library: most of the other integer arithmetic operation have such
informal assumptions.

Another source of panics is indexing. Indexing in an array, a slice or
a vector is a partial operation: the index might be out of range.

In the example folder of hax, you can find the [`chacha20`
example](https://github.com/cryspen/hax/blob/main/examples/chacha20/src/lib.rs)
that makes use of pre-conditions to prove panic freedom.

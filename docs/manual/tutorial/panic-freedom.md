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

```{.rust .playable }
fn square(x: u8) -> u8 {
    x * x
}
```

Though, if we try to verify this function, F\* is complaining about a
subtyping issue: F\* tells us that it is not able to prove that the
result of the multiplication `x * x` fits the range of `u8`. The
multiplication `x * x` might indeed be overflowing!

For instance, running `square(16)` panics: `16 * 16` is `256`, which
is just over `255`, the largest integer that fits `u8`. Rust does not
ensure that functions are *total*: a function might panic at any
point, or might never terminate.

## Panic freedom with Lean

Let's take the same `square` function and extract it to Lean using `cargo hax into lean`.
If we run `lake build` on the result, we get a success, but this doesn't mean that the function is 
panic-free. Indeed, our encoding of Rust code in Lean wraps everything in a result monad. And 
functions that panic return an error in this monad. To try to prove panic-freedom, we have to 
specify that the result of `square` is expected not to be an error in this result type. A way
to do that is the following:
```{.rust .playable .lean-backend}
#[hax_lib::lean::after("
theorem square_spec (value: u8) :
  ⦃ __requires (value) = pure true ⦄
  (square value)
  ⦃ ⇓ result => __ensures value result = pure true ⦄
  := by
  mvcgen
  simp [__requires, __ensures, square] at *
  intros
  rw [UInt8.HaxMul_spec_bv_rw] ; simp ;
  bv_decide")]
#[hax_lib::requires(true)]
#[hax_lib::ensures(|res| true)]
fn square(x: u8) -> u8 {
    x * x
}
```
The specification is extrinsic to the function, we state a theorem `square_spec` which uses a Hoare
triple to specify properties on the output, assuming some other properties on the inputs. Here,
we use the precondition and post-condition defined using the `hax_lib` macro, but we could write
our specification entirely in the `square_spec` theorem. Here our post-condition is `true` which seems
trivial, but `__ensures value result = pure true` is false if `result` (and thus `__ensures value result`) 
is an error in the result monad. So this specification states that `square` should be panic-free. We also 
have a small proof scripts applying a few tactics to try to prove our theorem. If we try running `lake build`
after extracting this code, we get an error: 
`The prover found a counterexample, consider the following assignment: value = 255`. Indeed `square(255)` 
panics.

## Rust and panicking code
Quoting the chapter [To `panic!` or Not to
`panic!`](https://doc.rust-lang.org/book/ch09-03-to-panic-or-not-to-panic.html)
from the Rust book:

> The `panic!` macro signals that your program is in a state it can't
> handle and lets you tell the process to stop instead of trying to
> proceed with invalid or incorrect values.

A Rust program should panics only in a situation where an assumption
or an invariant is broken: a panics models an *invalid* state. Formal
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

### Solution A: reflect the partialness of the function in Rust
A first solution is to make `square` return an `Option<u8>` instead of a `u8`:
``` {.rust .playable}
fn square_option(x: u8) -> Option<u8> {
    if x >= 16 {
        None
    } else {
        Some(x * x)
    }
}
```

Here, F\* is able to prove panic-freedom: calling `square` with any
input is safe. Though, one may argue that `square`'s input being small
enough should really be an assumption. Having to deal with the
possible integer overflowing whenever squaring is a huge burden. Can
we do better?

### Solution B: add a precondition
The type system of Rust doesn't allow the programmer to formalize the
assumption that `square` expects a small `u8`. This becomes
possible using hax: one can annotate a function with a pre-condition
on its inputs.

The pre-conditions and post-conditions on a function form a
*contract*: "if you give me some inputs that satisfies a given formula
(*the precondition*), I will produce a return value that satisfy
another formula (*the postcondition*)". Outside this contracts,
anything might happen: the function might panic, might run forever,
erase your disk, or anything.

The helper crate
[hax-lib](https://github.com/hacspec/hax/tree/main/hax-lib)
provdes the `requires`
[proc-macro](https://doc.rust-lang.org/reference/procedural-macros.html)
which lets user writting pre-conditions directly in Rust.

```{.rust .playable}
#[hax_lib::requires(x < 16)]
fn square_requires(x: u8) -> u8 {
    x * x
}
```

With this precondition, F\* is able to prove panic freedom. From now
on, it is the responsibility of the clients of `square` to respect the
contact. The next step is thus be to verify, through hax extraction,
that `square` is used correctly at every call site.

### Lean version of solution B
Let's try to add the precondition to the Lean version of the `square` function.
We can modify the Rust precondition:
```{.rust .playable .lean-backend}
#[hax_lib::lean::after("
theorem square_spec (value: u8) :
  ⦃ __requires (value) = pure true ⦄
  (square value)
  ⦃ ⇓ result => __ensures value result = pure true ⦄
  := by
  mvcgen
  simp [__requires, __ensures, square] at *
  intros
  rw [UInt8.HaxMul_spec_bv_rw] ; simp ;
  bv_decide")]
#[hax_lib::requires(x < 16)]
#[hax_lib::ensures(|res| true)]
fn square(x: u8) -> u8 {
    x * x
}
```
Now, extracting and then running Lean succeeds!

## Common panicking situations
Multiplication is not the only panicking function provided by the Rust
library: most of the other integer arithmetic operation have such
informal assumptions.

Another source of panics is indexing. Indexing in an array, a slice or
a vector is a partial operation: the index might be out of range.

In the example folder of hax, you can find the [`chacha20`
example](https://github.com/hacspec/hax/blob/main/examples/chacha20/src/lib.rs)
that makes use of pre-conditions to prove panic freedom.

Another solution for safe indexing is to use the [newtype index
pattern](https://matklad.github.io/2018/06/04/newtype-index-pattern.html),
which is [also supported by
hax](https://github.com/hacspec/hax/blob/d668de4d17e5ddee3a613068dc30b71353a9db4f/tests/attributes/src/lib.rs#L98-L126). The [data invariants](data-invariants.md#newtype-and-refinements) chapter gives more details about this.


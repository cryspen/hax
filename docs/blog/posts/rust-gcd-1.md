---
authors:
  - alex
title: "Verifying a real world Rust crate"
date: 2025-12-08
---

# Verifying a real world Rust crate

In this post,
we are going to use hax and F\* to verify a small real world Rust crate.
Then, we will try other verification tools (Kani, Verus, Aeneas) to the same thing.
The Rust crate [gcd](https://crates.io/crates/gcd) by Corey Farwell that we are going to verify implements
functions to compute the greatest common divisor of two integers.
We will focus on proving termination and panic freedom for now.
In a future post, we will look at functional correctness.

We have forked the repository [here](https://github.com/cryspen/rust-gcd).
The results of this tutorial can be found in different branches of this fork:

* [hax_fstar](https://github.com/cryspen/rust-gcd/tree/hax_fstar)
* [kani](https://github.com/cryspen/rust-gcd/tree/kani)
* [aeneas](https://github.com/cryspen/rust-gcd/tree/aeneas)
* [verus](https://github.com/cryspen/rust-gcd/tree/verus)

## Preparation

First, install Hax and F\*:

* [Install Hax](https://github.com/cryspen/hax?tab=readme-ov-file#installation) (We are using commit `0334b38`, so after `git clone git@github.com:cryspen/hax.git && cd hax`, run `git checkout 0334b38`)

* [Install F\*](https://github.com/FStarLang/FStar/blob/master/INSTALL.md)

To get started, we clone the repo of the Rust crate and switch to the
commit that we use in this post (`8fb3a59`):
```
git clone git@github.com:frewsxcv/rust-gcd.git && cd rust-gcd
git checkout 8fb3a59
```

We add hax-lib as a dependency, which will allow us to make annotations in the Rust code:
```
cargo add --git https://github.com/hacspec/hax hax-lib --rev 0334b38
```

## Extraction

Now we can attempt to translate the Rust code into F\* code, which we will later verify. Our Rust crate implements two variants to compute the greatest common divisor, the euclidean algorithm and the binary algorithm, each in various variants for different integer types. To start simple, we will focus on
the `u8` variant of the euclidean algorithm first. The following command instructs hax to extract only the function `gcd::euclid_u8` and its dependencies.
```
cargo hax into -i '-** +gcd::euclid_u8' fstar
```
This creates a new file `proofs/fstar/extraction/Gcd.fst`, which contains a translation of our Rust crate in F\*. To help F\* find the correct dependencies, we download [this Makefile](https://gist.githubusercontent.com/W95Psp/4c304132a1f85c5af4e4959dd6b356c3/raw/a54aec2538c625eb525281106ff73ea96f7b96dc/Makefile)
and put it into `proofs/fstar/extraction/`.

Before we instruct F\* to start proving anything, we first check that all dependencies can be found:
```
OTHERFLAGS="--lax" make -C proofs/fstar/extraction/
```
This yields some harmless warnings and eventually:
```
All verification conditions discharged successfully
```
This means that all dependencies are available and we can start proving things.

The Makefile we are using helps us to cache the results of the F\* verification, but this cache has the dangerous flaw that it does not invalidate when removing the `--lax` flag we used above. So we should delete the cache now:
```
rm -rf .fstar-cache
```

## Panic freedom of Euclidean GCD

By default, without us specifying anything, hax's F\* backend will attempt to prove that the Rust program terminates and does not panic:
```
make -C proofs/fstar/extraction/
```
The proof attempt fails with the following error:
```
* Error 19 at Gcd.fst(26,10-26,14):
  - Subtyping check failed
  - Expected type
      o:
      (Rust_primitives.Integers.u8 & Rust_primitives.Integers.u8)
        { (let _, _ = o in
            true) /\
          (let _, _ = o in
            Rust_primitives.Hax.Int.from_machine (Rust_primitives.Integers.mk_u32
                  0)
            <:
            Hax_lib.Int.t_Int) <
          (let _, _ = temp_0_ in
            Rust_primitives.Hax.Int.from_machine (Rust_primitives.Integers.mk_u32
                  0)
            <:
            Hax_lib.Int.t_Int) }
    got type Rust_primitives.Integers.u8 & Rust_primitives.Integers.u8
```
To prove that a while-loop terminates, F\* requires a measure that decreases with every loop iteration. By default, the measure is simply the number 0, which always fails and results in errors resembling the one above. We need to find a better expression that decreases with every loop iteration. The relevant while-loop is the following:
```rust
while b != 0 {
    let temp = a;
    a = b;
    b = temp;

    b %= a;
}
```
In each iteration, the variables `a` and `b` get swapped and `b` is then set to `b % a`. If we focus only on what is happening to `b` here, we observe that `b` is set to `a % b` over the course of one iteration. Since `b` is always smaller than `a % b`, `b` is decreasing with every iteration, and we can set it as our termination measure:
```rust
while b != 0 {
    hax_lib::loop_decreases!(b);
    let temp = a;
    a = b;
    b = temp;

    b %= a;
}
```
We extract the F\* code again and rerun F\*:
```
cargo hax into -i '-** +gcd::euclid_u8' fstar
make -C proofs/fstar/extraction/
```
We get:
```
[CHECK] Gcd.fst 
Verified module: Gcd
All verification conditions discharged successfully
```
So the `gcd::euclid_u8` function terminates on all inputs and never panics!

We would like to verify the other variants of this function for different bit lengths as well, but using
```
cargo hax into -i '-** +gcd::euclid_u8 +gcd::euclid_u16 +gcd::euclid_u32 +gcd::euclid_u64 +gcd::euclid_u128 +gcd::euclid_usize' fstar
```
is a bit inconvenient. Instead, we can also mark the functions that we want to extract in the Rust code using the `#[hax_lib::include]` annotation:
```rust
#[hax_lib::include]
pub const fn $euclid(a: $T, b: $T) -> $T
{
[...]
```
and then we can extract those functions using
```
cargo hax into -i '-**' fstar
```
You can open the the file `Gcd.fst` to make sure that all desired functions have indeed been extracted.
Now we can verify all variants, which should work without any further changes:
```
make -C proofs/fstar/extraction/
```

## Panic freedom of binary GCD

Next, we will attempt to prove panic freedom also for the binary variants. We add an `include`-annotation to the `$binary` function:
```rust
#[hax_lib::include]
pub const fn $binary(mut u: $T, mut v: $T) -> $T
{
[...]
```

We attempt to extract this function as well:
```
cargo hax into -i '-**' fstar
```

Unfortunately, it's not that easy. Hax can only translate a fragment of Rust. If something cannot be translated, we need to work around that. In our case, we get lots of errors of this kind:
```
error: [HAX0001] something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/933.
Please upvote or comment this issue if you see this error message.
Unhandled loop kind

This is discussed in issue https://github.com/hacspec/hax/issues/933.
Please upvote or comment this issue if you see this error message.
Note: the error was labeled with context `FunctionalizeLoops`.

  --> src/lib.rs:45:13
   |
45 | /             loop {
46 | |                 v >>= v.trailing_zeros();
...  |
58 | |                 if v == 0 { break; }
59 | |             }
   | |_____________^
   |
```
This is because the `loop`-construct cannot be translated. As a first (temporary) fix, we replace `loop` in `src/lib.rs` by `while true`.

We run extraction again:
```
cargo hax into -i '-**' fstar
```
Now it succeeds. We verify:
```
make -C proofs/fstar/extraction/
```
This yields a couple of harmless warnings and one error:
```
Error 72 at Gcd.fst(29,38-29,61):
  - Identifier impl_u8__trailing_zeros not found in module Core_models.Num
```
This is happening because the function `trailing_zeros` is missing in hax's F\* library. We can add it locally to our project by creating a file named `Core_models.Num.fsti` in `proofs/fstar/extraction`, and inserting the following code:
```fstar
module Core_models.Num
open Rust_primitives
 
val trailing_zeros: #t:inttype -> int_t t -> (n:u32{v n >= 0 /\ v n <= bits t})

unfold let impl_u8__trailing_zeros (n:u8) = trailing_zeros n
unfold let impl_u16__trailing_zeros (n:u16) = trailing_zeros n
unfold let impl_u32__trailing_zeros (n:u32) = trailing_zeros n
unfold let impl_u64__trailing_zeros (n:u64) = trailing_zeros n
unfold let impl_u128__trailing_zeros (n:u128) = trailing_zeros n
unfold let impl_usize__trailing_zeros (n:usize) = trailing_zeros n
```
This code tells F\* about the `trailing_zeros` functions and their signature for all unsigned integer types.

Running verification again, we get the next error:
```
* Error 72 at Gcd.fst(19,28-19,41):
  - Identifier while_loop_cf not found in module Rust_primitives.Hax
```
This is another missing function in hax's F\* libraries ([issue #1204](https://github.com/cryspen/hax/issues/1204)).
We can avoid it by refactoring the Rust code such that it avoids `break`s in while-loops.
Here is the problematic while-loop:
```rust
pub const fn $binary(mut u: $T, mut v: $T) -> $T
{
    if u == 0 { return v; }
    if v == 0 { return u; }

    let shift = (u | v).trailing_zeros();
    u >>= shift;
    v >>= shift;
    u >>= u.trailing_zeros();

    while true {
        v >>= v.trailing_zeros();

        if u > v {
            let temp = u;
            u = v;
            v = temp;
        }

        v -= u;

        if v == 0 { break; }
    }

    u << shift
}
```
So how can we get rid of the `break`? We will have to modify the Rust code a little.
We will try to move the line `if v == 0 { break; }` further up.
Since `v - u == 0` if and only if `u == v`, we can check for that
before the assignment `v -= u`:
```rust
while true {
    v >>= v.trailing_zeros();

    if u > v {
        let temp = u;
        u = v;
        v = temp;
    }

    if u == v { break; }

    v -= u;
}
```
Moreover, for the condition `u == v` it does not matter
whether `u` and `v` are swapped. So we can also move the check before the swapping:
```rust
while true {
    v >>= v.trailing_zeros();

    if u == v { break; }

    if u > v {
        let temp = u;
        u = v;
        v = temp;
    }

    v -= u;
}
```
Since the loop-condition is always true, we can do the
assignment `v >>= v.trailing_zeros();` just as well at the end of every iteration instead of the beginning of each iteration
if we perform it one additional time before the loop starts:
```rust
v >>= v.trailing_zeros();
while true {
    if u == v { break; }

    if u > v {
        let temp = u;
        u = v;
        v = temp;
    }

    v -= u;
    v >>= v.trailing_zeros();
}
```
Finally, we can move the line `if u == v { break; }` into the loop's condition:
```rust
v >>= v.trailing_zeros();
while u != v {

    if u > v {
        let temp = u;
        u = v;
        v = temp;
    }

    v -= u;
    v >>= v.trailing_zeros();
}
```
Extracting and running F\* now yields:
```
* Error 19 at Gcd.fst(15,23-15,28):
  - Subtyping check failed
  - Expected type
      b:
      Rust_primitives.Integers.int_t Rust_primitives.Integers.U32
        { Rust_primitives.Integers.v b >= 0 /\
          Rust_primitives.Integers.v b <
          Rust_primitives.Integers.bits Rust_primitives.Integers.U8 }
    got type Rust_primitives.Integers.u32
```
This error occurs because the F\* specification of the `>>`-function expects its right-hand argument to be smaller than the total number of bits of the employed integer type. This is already the case in our code, but F\* is not able to figure out that the value `shift` is indeed small enough.

Most right-shifts in our code are by the number of trailing zeros of the given integer. That number of zeros can in principle be equal to the number of bits of the integer (which would be to large for `>>`), but only if the integer is `0`. So we can help F\* to figure out that everything is okay by adding the following lemma to `Core_models.Num.fsti`:

```fstar
val trailing_zeros_lt_bits #t (a: int_t t):
    Lemma (requires (v a <> 0))
          (ensures (v (trailing_zeros a) < bits t))
          [SMTPat (trailing_zeros a)]
```
The lemma states that the number of trailing zeros is smaller than the total number of bits whenever the integer is nonzero.
The `SMTPat`-annotation tells F\* that this lemma should be considered whenever a problem contains the `trailing_zeros` function.

However, there are also two occurrences of `>>` where we shift `u` and `v` by `(u | v).trailing_zeros()`. For these, we need the following additional lemmas:
```fstar
val trailing_zeros_band_le_left #t (a b : int_t t):
    Lemma (v (trailing_zeros (a |. b)) <= v (trailing_zeros a))
          [SMTPat (trailing_zeros (a |. b))]

val trailing_zeros_band_le_right #t (a b : int_t t):
    Lemma (v (trailing_zeros (a |. b)) <= v (trailing_zeros b))
          [SMTPat (trailing_zeros (a |. b))]
```
These lemmas state that the trailing zeros of `a |. b` will always be at most as many as the trailing zeros of `a`, and similarly for `b`. Via `SMTPat`, we tell F\* to use this lemma when it encounters expressions of the form `trailing_zeros (a |. b)`.

Since our first lemma applies only when the integer is nonzero, we also need to enable F\* to know that our integers do not become zero by shifting:
```fstar
val shift_right_trailing_zeros_nonzero #t (a: int_t t) (b : u32):
    Lemma (requires (v a <> 0) && (v b <= v (trailing_zeros a)))
          (ensures (v (shift_right a b) <> 0))
          [SMTPat (shift_right a b)]
```

This resolves the error around `>>`.

Finally, we need to add a termination measure to the while-loop.
This is the loop:
```rust
while u != v {

    if u > v {
        let temp = u;
        u = v;
        v = temp;
    }

    v -= u;
    v >>= v.trailing_zeros();
}
```

Here is a summary of what the while loop is doing: It subtracts the smaller number among `u` and `v` from the larger one among them.
Then, it removes any trailing zeros from the result.
So in each iteration, as long as both numbers are nonzero, the larger one of the two numbers will definitely get smaller, and the other one will remain the same.
Therefore, we will use the larger number among `u` and `v` as our termination measure:
```rust
while u != v {
    hax_lib::loop_decreases!(if v < u { u } else { v });

    if u > v {
        let temp = u;
        u = v;
        v = temp;
    }

    v -= u;
    v >>= v.trailing_zeros();
}
```
Since subtracting `0` does not decrease the number,
it is cruicial that `v` and `u` do not become `0`. We annotate the loop with this invariant to make F\* aware of this:
```rust
while u != v {
    hax_lib::loop_decreases!(if v < u { u } else { v });
    hax_lib::loop_invariant!(v != 0 && u != 0);

    if u > v {
        let temp = u;
        u = v;
        v = temp;
    }

    v -= u;
    v >>= v.trailing_zeros();
}
```
We also need to make F\* aware that `v >>= v.trailing_zeros();` cannot
increase `v` with an additional lemma:
```fstar
val shift_right_trailing_zeros_le #t (a: int_t t):
    Lemma (requires (v a <> 0))
          (ensures (v (shift_right a (trailing_zeros a)) <= v a))
          [SMTPat (shift_right a (trailing_zeros a))]
```
We extract and reverify:
```
[CHECK] Gcd.fst 
Verified module: Gcd
All verification conditions discharged successfully
```
Yay, we made it! Also the binary implementation always terminates and never panics.

## Verification using other tools

For comparison, we verify panic freedom and termination
using other tools as well.

### Kani

First, [install Kani](https://model-checking.github.io/kani/install-guide.html). We will use version 0.66.0.

To verify the function `$euclid` using Kani,
we need to add another function that implements the verification. Since `$euclid` is part of a macro `gcd_impl`
that duplicates it for various bit-lengths,
we add a third identifier `$check_euclid:ident` to that macro,
and provide the following identifiers:
```rust
gcd_impl! {
    (u8) binary_u8 euclid_u8 check_euclid_u8,
    (u16) binary_u16 euclid_u16 check_euclid_u16,
    (u32) binary_u32 euclid_u32 check_euclid_u32,
    (u64) binary_u64 euclid_u64 check_euclid_u64,
    (u128) binary_u128 euclid_u128 check_euclid_u128,
    (usize) binary_usize euclid_usize check_euclid_usize
}
```
Now we can implement the verification function `check_gcd` inside the macro. Here is a first draft:
```rust
#[kani::proof]
#[cfg(kani)]
fn $check_gcd() {
    let x: $T = kani::any();
    let y: $T = kani::any();

    $euclid(x, y);
}
```
The first annotation tells Kani to run this verification function, and the second annotation tells the normal Rust compiler to ignore this function. The expression `kani::any()` tells Kani to test all possible integer values for `x` and `y`.

Now we run Kani:
```
kani ./src/lib.rs 
```
Unfortunatlely, Kani does not terminate because the loop in `$euclid` is potentially unbounded.

#### Unwinding bound

We need to specify an upper bound on how often we want Kani to unwind the loop, using the `kani::unwind` annotation. When setting such an upper bound, we also need to limit the variables `x` and `y` to values that will make the number of loop iterations stay below the given bound, using `kani::assume`. Here are some numbers that work okay:
```rust
#[kani::proof]
#[cfg(kani)]
#[kani::unwind(15)]
fn $check_euclid() {
    let limit: u128 = 200;
    let x: $T = kani::any();
    let y: $T = kani::any();
    kani::assume((x as u128) < limit);
    kani::assume((y as u128) < limit);

    let res = $euclid(x, y);
}
```
Now we run `kani ./src/lib.rs` again:
```
Complete - 12 successfully verified harnesses, 0 failures, 12 total.
```
The binary version can be verified in the exact same way by adding an analogous verification function `$check_binary` to the macro.

#### Loop contracts
However, there is yet another option to verify loops in Kani, without the need to limit the verified input values: loop contracts.

To use them, we first need to add the following
annotations at the top of our file:
```rust
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]
```

Now we can use the annotation `kani::loop_invariant` to annotate our loop with an invariant. Since we only want to show panic-freedom here, simple using `true` works as an invariant for the loop in `$euclid`:
```rust
#[kani::loop_invariant(true)]
while b != 0 {
    let temp = a;
    a = b;
    b = temp;

    b %= a;
}
```
With this annotation, Kani will abstract over the loop instead of unwinding it. So we no longer need to
limit the size of our inputs in `$check_euclid`. We can comment out the corresponding lines:
```rust
// kani::assume(x < limit);
// kani::assume(y < limit);
```
To activate the loop contract feature we need to add
the following option when invoking Kani:
```
kani ./src/lib.rs -Z loop-contracts
```
Now verification is much faster, and it verifies all possible inputs:
```
Complete - 12 successfully verified harnesses, 0 failures, 12 total.
```
However, in contrast to the approach without loop contracts, this does not verify termination!

Similarly, we can also verify the function `$binary` using loop contracts. However, using `true` as an invariant does not work here because the line
```rust
v >>= v.trailing_zeros();
```
can panic when `v` is `0`.
So we add `v != 0` as an invariant:
```rust
#[kani::loop_invariant(v != 0)]
loop {
    v >>= v.trailing_zeros();

    #[allow(clippy::manual_swap)]
    if u > v {
        // mem::swap(&mut u, &mut v);
        let temp = u;
        u = v;
        v = temp;
    }

    v -= u; // here v >= u

    if v == 0 { break; }
}
```

*What's to love:* Kani requires amazingly little manual labor to set up!


### Verus

[Install Verus](https://github.com/verus-lang/verus/blob/main/INSTALL.md).
(We use version `0.2025.11.07.a99b6c7`.)

To start verifying with Verus,
we add the following import to `src/lib.rs`:
```rust
use vstd::prelude::*;
```
And we wrap the function `$euclid` that we would like to verify into
```rust
verus! {

}
```
Now we can try to run Verus:
```
verus src/lib.rs --crate-type=lib
```
We get:
```
error: loop must have a decreases clause
```
From our discussion above, we know that the variable `b` decreases in the loop. Let's tell Verus about that:
```rust
while b != 0 decreases b {
    let temp = a;
    a = b;
    b = temp;

    b %= a;
}
```
Running Verus again now yields:
```
verification results:: 12 verified, 0 errors
```
The `$euclid` function terminates and is panic-free!

Next, we wrap the `$binary` function into `verus! { ... }` as well.
Running Verus now results in an error:
```
error: `core::num::impl&%11::trailing_zeros` is not supported
```
The `trailing_zeros` function is present in Verus's library, but only for certain bit sizes. We could add the missing functions, but to simplify things, let's simply comment out the large bit sizes:
```rust
gcd_impl! {
    (u8) binary_u8 euclid_u8,
    (u16) binary_u16 euclid_u16,
    (u32) binary_u32 euclid_u32,
    (u64) binary_u64 euclid_u64//,
    // (u128) binary_u128 euclid_u128,
    // (usize) binary_usize euclid_usize
}
```
and
```rust
gcd_impl_nonzero! {
    (NonZeroU8) binary_nonzero_u8/binary_u8 euclid_nonzero_u8/euclid_u8,
    (NonZeroU16) binary_nonzero_u16/binary_u16 euclid_nonzero_u16/euclid_u16,
    (NonZeroU32) binary_nonzero_u32/binary_u32 euclid_nonzero_u32/euclid_u32,
    (NonZeroU64) binary_nonzero_u64/binary_u64 euclid_nonzero_u64/euclid_u64//,
    // (NonZeroU128) binary_nonzero_u128/binary_u128 euclid_nonzero_u128/euclid_u128,
    // (NonZeroUsize) binary_nonzero_usize/binary_usize euclid_nonzero_usize/euclid_usize
}
```
The next error that we get is:
```
error: loop must have a decreases clause
```
Let us reuse the same measure as we have used for Hax:
```rust
loop
    decreases if v < u { u } else { v }
{
    v >>= v.trailing_zeros();

    if u > v {
        let temp = u;
        u = v;
        v = temp;
    }

    v -= u; // here v >= u

    if v == 0 { break; }
}
```

Our next error is:
```
error: possible bit shift underflow/overflow
   --> src/lib.rs:45:13
    |
45  |               u >>= shift;
```
We can make our lives easier by simply commenting
out the two lines
```rust
u >>= shift;
v >>= shift;
```
Note that this does not change the function's behavior.
The following line and the first line of the loop
will shift `v` and `u` by all trailing zeros anyway.
There is no need to shift them by their common trailing
zeros before that.

With those lines commented out, we now get:
```
error: decreases not satisfied at end of loop
```
Our measure does actually decrease, but Verus is unable to prove it. First, we need to add a loop invariant
that `u` and `v` are nonzero. If one of them was zero, then subtracting one from the other would not make the measure decrease.
```rust
loop
    invariant_except_break u != 0 && v != 0
    decreases if v < u { u } else { v }
{   
```
Also, Verus has trouble figuring out
that the line
```
v >>= v.trailing_zeros();
```
will never make `v` larger and will never cause `v` to become `0`.
We can add the following assumptions to
fix this temporarily:
```
assume(v != 0 ==> v >> v.trailing_zeros() != 0);
assume(forall |i: u8| v >> i <= v);
v >>= v.trailing_zeros();
```
The next error we get is:
```
error: invariant not satisfied before loop
   --> src/lib.rs:50:40
    |
50  |                   invariant_except_break u != 0 && v != 0
```
This is because Verus cannot see that
```
u >>= u.trailing_zeros();
```
cannot make `u` become zero.
We can fix this temporarily using another assumption:
```rust
assume(u != 0 ==> u >> u.trailing_zeros() != 0);
u >>= u.trailing_zeros();
```
The only remaining error is:
```
error: possible bit shift underflow/overflow
   --> src/lib.rs:71:13
    |
71  |               u << shift
```
This error occurs because shift could in principle be equal to the full number of bits of `u` when `u | v` is zero.
Adding the following assumption above the definition of `shift`, helps Verus figure out that this cannot happen:
```rust
assume(u != 0 && v != 0 ==> u | v != 0);
let shift = (u | v).trailing_zeros();
```
Now verification succeeds:
```
$ verus src/lib.rs --crate-type=lib
verification results:: 16 verified, 0 errors
```
However, this confirms termination
and panic freedom only up to the assumptions we have inserted using `assume`.

Let's try to prove them.
The `bit_vector` tactic can prove some of them:
```
assert(u != 0 && v != 0 ==> u | v != 0) by (bit_vector);
```
and
```
assert(forall |i: u8| v >> i <= v) by (bit_vector);
```
We can use these lines to replace the corresponding `assume`s.

The remaining two `assume`s are harder to prove.
We will simply add them as an axiom by adding the following
function to our `gcd_impl` macro:
```
#[verifier::external_body]
proof fn $trailing_zeros_axiom(x: $T) 
    ensures x != 0 ==> x >> #[trigger] x.trailing_zeros() != 0
{}
```
Then, we can replace
the two remaining assumes by
```
proof! { $trailing_zeros_axiom(u); }
```
and
```
proof! { $trailing_zeros_axiom(v); }
```

*What's to love:* Verus allows us to work directly with the Rust code!

### Aeneas

[Install Aeneas](https://github.com/AeneasVerif/aeneas?tab=readme-ov-file#installation--build).
We use commit `f2fbd655` here.

[Install Lean](https://lean-lang.org/install/). 

We will use the following `Makefile` to make Aeneas extract Lean code from our crate:
```
CHARON_HOME	?= $(dir $(abspath $(lastword $(MAKEFILE_LIST))))/../charon
AENEAS_HOME	?= $(dir $(abspath $(lastword $(MAKEFILE_LIST))))/../aeneas

CHARON_EXE = $(CHARON_HOME)/bin/charon
AENEAS_EXE = $(AENEAS_HOME)/bin/aeneas

AENEAS_OPTIONS ?=

.PHONY: extract
extract: gcd.llbc
	$(AENEAS_EXE) -backend lean gcd.llbc -split-files -dest proofs/Gcd $(AENEAS_OPTIONS)

gcd.llbc: $(wildcard */*.rs)
	RUSTFLAGS="--cfg eurydice" $(CHARON_EXE) cargo --preset=aeneas --start-from crate::euclid_u8 --start-from crate::binary_u8
```
Save this under the name `Makefile` and run `make`. Note that we specify the options `--start-from crate::euclid_u8 --start-from crate::binary_u8`, which will extract specifically the functions `euclid_u8` and `binary_u8` into Lean. Running `make` produces a couple of Lean files in the directory `proofs/Gcd`.

We create a new Lean project around these files:
```
cd proofs
lake +v4.24.0 init Gcd lib
```

Add the following lines to `lakefile.toml` to
add the Aeneas Lean library as a dependency, adjusting the path as needed:
```toml
[[require]]
name = "aeneas"
path = "../../aeneas/backends/lean"
```
Then run
```
lake update
```
to update the dependencies. This will download `mathlib`,
a dependeny of Aeneas, which may take a while.

Aeneas created a file called `FunsExternal_Template.lean`
because the `trailing_zeros` function is not part of the Aeneas library. Rename this template file to `FunsExternal.lean`. We could write a precise definition of this function here, but for now, we just define it as `sorry`, which is a placeholder for a missing definition.
Replace the line
```lean
axiom core.num.U8.trailing_zeros : U8 → Result U32
```
by
```lean
def core.num.U8.trailing_zeros : U8 → Result U32 := sorry
```
Now in the root file of our Lean project, `Gcd.lean`, add the import
```
import Gcd.Funs
```
Now we run
```
lake build
```
to ensure that our Lean code typechecks:
```
warning: Gcd/FunsExternal.lean:15:4: declaration uses 'sorry'
Build completed successfully (1500 jobs).
```

Let's have a look at how the Lean translations of our Rust functions look like.
Open the file `Funs.lean` in VSCode (with the Lean extension installed). You may see a lot of red in the editor, which will go away by pressing `Restart file`.
The file contains four definitions: The functions `binary_u8` and `euclid_u8` themselves, and for each of them a function representing the contained loop, which has become a recursive function in Lean.

The `euclid_u8` funciton for example looks as follows:
```lean
/- [gcd::euclid_u8]: loop 0:
   Source: 'src/lib.rs', lines 75:12-82:13 -/
def euclid_u8_loop (a : U8) (b : U8) : Result U8 := do
  if b != 0#u8
  then let b1 ← a % b
       euclid_u8_loop b b1
  else ok a
partial_fixpoint

/- [gcd::euclid_u8]:
   Source: 'src/lib.rs', lines 65:8-85:9 -/
def euclid_u8 (a : U8) (b : U8) : Result U8 := do
  let (a1, b1) ← if a > b
                   then ok (a, b)
                   else ok (b, a)
  euclid_u8_loop a1 b1
```

#### Euclidean GCD

Now we can start proving. Open the file `Gcd.lean`.
Let us verify termination and panic-freedom of `euclid_u8`.
This can be expressed in Lean as follows:
```
theorem euclid_u8_spec (a b : U8) :
    ∃ y, euclid_u8 a b = ok y := by sorry
```
Here, the `sorry` stands for a missing proof.
A typical Aeneas proof looks like this:
```
theorem euclid_u8_spec (a b : U8) :
    ∃ y, euclid_u8 a b = ok y := by
  unfold euclid_u8
  progress*
```
Unfortunately, this proof does not quite work yet.
We get the error:
```
unsolved goals
case isTrue
a b : U8
h✝ : a > b
⊢ ∃ y, euclid_u8_loop a b = ok y

case isFalse
a b : U8
h✝ : ¬a > b
⊢ ∃ y, euclid_u8_loop b a = ok y
```
The problem is that the `progress*` tactic does
not know the specification of the `euclid_u8_loop` function.
Let's create a seperate theorem about that function.
Put the following code above the theorem that we just wrote:
```lean
@[progress]
theorem euclid_loop_u8_spec (a b : U8) :
    ∃ y, euclid_u8_loop a b = ok y := by sorry
```
This theorem states that `euclid_u8_loop` terminates and does not panic, for now without proof (`sorry`).
Note that after adding this theorem, the error on the theorem below has disappeared.
The annotation `@[progress]` informs the `progress*` tactic about this specification and it can be used in the proof of `euclid_u8_spec`.

Now we need to replace the `sorry` with an actual proof.
Let's try the same idea:
```lean
@[progress]
theorem euclid_loop_u8_spec (a b : U8) :
    ∃ y, euclid_u8_loop a b = ok y := by 
  unfold euclid_u8_loop
  progress*
```

We get an error:
```
fail to show termination for
  gcd.euclid_loop_u8_spec
```

From our discussion above, we know that `b` is a variable that decreases in this recursive function. We can tell Lean about this as follows:
```lean
@[progress]
theorem euclid_loop_u8_spec (a b : U8) :
    ∃ y, euclid_u8_loop a b = ok y := by 
  unfold euclid_u8_loop
  progress*
termination_by b.val
decreasing_by scalar_decr_tac
```

Now all errors have disappeared and there are little check marks in the margin. That means `euclid_u8` really terminates and is panic-free!

#### Binary GCD

Now, let's try to verify the binary version as well.
The Lean translation looks like this:
```lean
/- [gcd::binary_u8]: loop 0:
   Source: 'src/lib.rs', lines 45:12-59:13 -/
def binary_u8_loop (u : U8) (v : U8) : Result U8 := do
  let i ← core.num.U8.trailing_zeros v
  let v1 ← v >>> i
  let (u1, v2) ← if u > v1
                   then ok (v1, u)
                   else ok (u, v1)
  let v3 ← v2 - u1
  if v3 = 0#u8
  then ok u1
  else binary_u8_loop u1 v3
partial_fixpoint

/- [gcd::binary_u8]:
   Source: 'src/lib.rs', lines 35:8-62:9 -/
def binary_u8 (u : U8) (v : U8) : Result U8 := do
  if u = 0#u8
  then ok v
  else
    if v = 0#u8
    then ok u
    else
      let i ← (↑(u ||| v) : Result U8)
      let shift ← core.num.U8.trailing_zeros i
      let u1 ← u >>> shift
      let v1 ← v >>> shift
      let i1 ← core.num.U8.trailing_zeros u1
      let u2 ← u1 >>> i1
      let u3 ← binary_u8_loop u2 v1
      u3 <<< shift
```
We use the same approach as for `euclid_u8`, adding the following code to `Gdc.lean`:
```lean
theorem binary_u8_spec (a b : U8) :
    ∃ y, binary_u8 a b = ok y := by
  unfold binary_u8
  progress*
```
We get the following error:
```
unsolved goals
a b : U8
h✝¹ : ¬a = 0#u8
h✝ : ¬b = 0#u8
i : U8
_ : [> let i ← ↑(a ||| b) <]
i_post_1 : ↑i = ↑(a ||| b)
i_post_2 : i.bv = a.bv ||| b.bv
⊢ ∃ y,
  (do
      let shift ← core.num.U8.trailing_zeros i
      let u1 ← a >>> shift
      let v1 ← b >>> shift
      let i1 ← core.num.U8.trailing_zeros u1
      let u2 ← u1 >>> i1
      let u3 ← binary_u8_loop u2 v1
      u3 <<< shift) =
    ok y
```
The `progress*` tactic gets stuck at `core.num.U8.trailing_zeros` because there is no specification about this function.
Let's provide one, for instance directly above `binary_u8_spec`:
```lean
@[progress]
theorem trailing_zeros_spec (v : U8) (hv : v ≠ 0#u8):
  ∃ y, core.num.U8.trailing_zeros v = .ok y ∧ y < 8#u32 := sorry
```
Here, we have added the fact that `trailing_zeros` will be less than the bit length when the input is nonzero
since we have seen above that this is crucial for verification of binary GCD.

Next, we get the error:
```
unsolved goals
case hv
a b : U8
h✝¹ : ¬a = 0#u8
h✝ : ¬b = 0#u8
i : U8
_ : [> let i ← ↑(a ||| b) <]
i_post_1 : ↑i = ↑(a ||| b)
i_post_2 : i.bv = a.bv ||| b.bv
⊢ i ≠ 0#u8
```
The tactic gets stuck because there is no specification saying that bitwise or (`|||`) will not yield zero when the inputs are nonzero.
Let's add that:
```lean
@[progress]
theorem bor_spec (u v : U8) (hu : u ≠ 0#u8) (hv : v ≠ 0#u8) :
  ∃ y, (↑(u ||| v) : Result U8) = .ok y ∧
    y ≠ 0#u8 := sorry
```

The next error is:
```
unsolved goals
case hv
a b : U8
h✝¹ : ¬a = 0#u8
h✝ : ¬b = 0#u8
i : U8
_✝² : [> let i ← ↑(a ||| b) <]
i_post : i ≠ 0#u8
shift : U32
_✝¹ : [> let shift ← core.num.U8.trailing_zeros i <]
shift_post : shift < 8#u32
u1 : U8
_✝ : [> let u1 ← a >>> shift <]
u1_post_1 : ↑u1 = ↑a >>> ↑shift
u1_post_2 : u1.bv = a.bv >>> ↑shift
v1 : U8
_ : [> let v1 ← b >>> shift <]
v1_post_1 : ↑v1 = ↑b >>> ↑shift
v1_post_2 : v1.bv = b.bv >>> ↑shift
⊢ u1 ≠ 0#u8
```

Here, we need to tell Lean that right shifting by the number of trailing zeros (or less) will not turn a nonzero number into zero.
Here is a first attempt to state that:
```lean
@[progress]
theorem shift_right_spec (u : U8) (v : U32) (hu : u ≠ 0#u8) (hv : v ≤ core.num.U8.trailing_zeros u):
  ∃ y, u >>> v = .ok y ∧ y ≠ 0#u8 := sorry
```
Unfortunately, this does not work because `core.num.U8.trailing_zeros` lives in the `Result` monad, i.e., it's type is `U8 → Result U32`, not `U8 → U32`.
To get around this issue, we define another function `trailing_zeros`:
```lean
def trailing_zeros : U8 → U32 := sorry
```
Since implementing it is beyond the scope of this blog post, we use the placeholder `sorry`.
Now, we extend our specification of `core.num.U8.trailing_zeros` to state that it will always return the same result as prescibed by our new `trailing_zeros` function:
```lean
@[progress]
theorem trailing_zeros_spec (v : U8) (hv : v ≠ 0#u8):
  ∃ y, core.num.U8.trailing_zeros v = .ok y ∧ y < 8#u32 ∧ y = trailing_zeros v := sorry
```
Then we can fix the specification of right-shift using our new function:
```lean
@[progress]
theorem shift_right_spec (u : U8) (v : U32) (hu : u ≠ 0#u8) (hv : v ≤ trailing_zeros u):
  ∃ y, u >>> v = .ok y ∧ y ≠ 0#u8 := sorry
```
The next error is this:
```
unsolved goals
case hv
a b : U8
h✝¹ : ¬a = 0#u8
h✝ : ¬b = 0#u8
i : U8
_✝ : [> let i ← ↑(a ||| b) <]
i_post : i ≠ 0#u8
shift : U32
_ : [> let shift ← core.num.U8.trailing_zeros i <]
shift_post_1 : shift < 8#u32
shift_post_2 : shift = trailing_zeros i
⊢ shift ≤ trailing_zeros a
```
What's missing here, is that bitwise or (`|||`) will always yield less trailing zeros than in the inputs.
We can edit the specification of bitwise or to fix that:
```lean
@[progress]
theorem bor_spec (u v : U8) (hu : u ≠ 0#u8) (hv : v ≠ 0#u8) :
  ∃ y, (↑(u ||| v) : Result U8) = .ok y ∧
    trailing_zeros y ≤ trailing_zeros u ∧
    trailing_zeros y ≤ trailing_zeros v ∧
    y ≠ 0#u8 := sorry
```
Next, the tactic gets stuck on:
```
⊢ ∃ y,
  (do
      let u3 ← binary_u8_loop u2 v1
      u3 <<< shift) =
    ok y
```
This is because we don't have a specification for `binary_u8_loop` yet. Let's add one:
```lean
@[progress]
theorem binary_u8_loop_spec (a b : U8) :
    ∃ y, binary_u8_loop a b = ok y := by
  unfold binary_u8_loop
  progress*
termination_by max a.val b.val
decreasing_by all_goals scalar_decr_tac
```
Since the tactic is recursive, we need to provide a measure for termination. We'll use the maximum of `a` and `b`, just like we have done above.
We add `all_goals` because `decreasing_by` is decreasing two goals here.
This still fails because we are missing two more things:
First, we need to extend or specification of right-shift to state that it will make the input smaller:
```
@[progress]
theorem shift_right_spec (u : U8) (v : U32) (hu : u ≠ 0#u8) (hv : v ≤ trailing_zeros u):
  ∃ y, u >>> v = .ok y ∧ y ≠ 0#u8 ∧ y ≤ u := sorry
```
Second, we need to add what corresponds to a loop invariant in the specification of `binary_u8_loop`:
```lean
@[progress]
theorem binary_u8_loop_spec (a b : U8) (ha : a ≠ 0#u8) (hb : b ≠ 0#u8) :
    ∃ y, binary_u8_loop a b = ok y ∧ y ≠ 0#u8 := by
  unfold binary_u8_loop
  progress*
termination_by max a.val b.val
decreasing_by all_goals scalar_decr_tac
```
No more errors! So Aeneas, too, agrees that `binary_u8` terminates and does not panic.

*What's to love:* Aeneas leaves our source code completely untouched!

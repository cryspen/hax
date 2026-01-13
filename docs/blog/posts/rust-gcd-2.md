---
authors:
  - alex
title: "Verifying a real world Rust crate"
date: 2026-01-13
---

# Verifying a while loop in Hax/Lean

In our last blog post, the dog that didn't bark was Hax/Lean. It was missing because we did not have support for while loops then. Now, we support them and we will demonstrate it here.

You can find the results of this tutorial
on [https://github.com/cryspen/rust-gcd/tree/hax_lean1](https://github.com/cryspen/rust-gcd/tree/hax_lean1) on the branch `hax_lean1`.

## Preparation

First, we need to install Hax and Lean:

* [Hax](https://github.com/cryspen/hax?tab=readme-ov-file#installation)
(We are using commit `d1365d4`, so after `git clone git@github.com:cryspen/hax.git && cd hax`, run `git checkout d1365d4`)

* [Lean](https://lean-lang.org/install/)

Again, we will use the [gcd Rust crate](https://github.com/frewsxcv/rust-gcd) as an example:
```
git clone git@github.com:frewsxcv/rust-gcd.git && cd rust-gcd
git checkout 8fb3a59
```
We add hax-lib as a dependency, which will allow us to make annotations in the Rust code:
```
cargo add --git https://github.com/hacspec/hax hax-lib --rev d1365d4
```

## Extraction

Now we are ready to translate the Rust code into Lean code. We will limit ourselves to
the `euclid_u16` function here:
```
cargo hax into -i '-** +gcd::euclid_u16' lean
```
This will create a new file `proofs/lean/extraction/Gcd.lean` containing the Lean version of
the extracted function.

For Lean to find the required dependencies, 
we must add the following two files in `proofs/lean`:


`lean-toolchain`:
```
leanprover/lean4:v4.23.0
```

`lakefile.toml`:
```
name = "Gcd"
version = "0.1.0"
defaultTargets = ["Gcd"]

[[lean_lib]]
name = "Gcd"
roots = ["extraction.Gcd"]

[[require]]
name = "Hax"
path = "../../../hax/hax-lib/proof-libs/lean"
```
Make sure that the path above points to the subdirectory `hax-lib/proof-libs/lean` of the repository that you checked out during the installation of Hax (i.e., `git@github.com:cryspen/hax.git` on commit `d1365d4`). The path can be relative to the `lakefile.toml` file or absolute.

Now we can run Lean on the extracted code.
```
(cd proofs/lean && lake build)
```
It should take a moment and then say:
```
Build completed successfully (35 jobs).
```
So it this already verified? No, currently, we need to add a pre- or post-condition to
a function to make Hax generate a specification that we can prove correct. (This will likely change in the near future.)

## Verification

We can add the following `hax_lib::ensures` annoation 
above the definition of `$euclid`
to say that we want to prove termination and panic-freedom:
```
#[hax_lib::ensures(|_| true)]
pub const fn $euclid(a: $T, b: $T) -> $T
{
    ...
}
```
We run Hax and Lean again:
```
cargo hax into -i '-** +gcd::euclid_u16' lean
(cd proofs/lean && lake build)
```
Now, we get lots of `unsolved goals` errors.
We can open the `Gcd.lean` file to get a better impression of what is going on.
The file contains a definition of `Gcd.euclid_u16`, which is the Lean version of our `euclid_u16` function and which compiles without error.
Below, we have a definition of `Gcd.euclid_u16.spec`,
which contains the specification of the function and an attempted proof of correctness.
It should have a red squiggly underline on the `contract` proof,
indicating that the error occurs there.
The default proof `by mvcgen[Gcd.euclid_u16] <;> try grind` fails.

If we click just behind `mvcgen[Gcd.euclid_u16]`, we can see the verification conditions
that Lean's `mvcgen` tactic generated in Lean's infoview.
It shows a list of four goals.
The second and the forth goal end in:
```
ToNat.toNat 0 < ToNat.toNat 0
```
So this says that the `u16` value `0`, converted to a natural number, is smaller than itself.
This is simply wrong and will be impossible to prove.
These verification conditions are coming from the default termination measure associated with while loops, which is constant `0` by default. We will have to provide a better measure to prove termination, using the `hax_lib::loop_decreases` annotation.
From our last blog post, we know that `b` is a useful measure for this loop:
```
while b != 0 {
    hax_lib::loop_decreases!(b);
    // mem::swap(&mut a, &mut b);
    let temp = a;
    a = b;
    b = temp;

    b %= a;
}
```
After running Hax and Lean again, the default proof still fails,
but the generated verification conditions can now be proved with some manual effort.
After developing the proof in Lean, we can copy the proof into the Rust file
so that it does not get overwritten when reextracting the code:
```
#[hax_lib::ensures(|_| true)]
#[hax_lib::lean::proof("by
    mvcgen[Gcd.euclid_u16]
    · expose_names
      intro
      simp_all [a_1]
    · expose_names
      simp only [ToNat.toNat, h_4]
      apply Nat.mod_lt
      grind
    · expose_names
      intro
      simp_all [a_1]
    · expose_names
      simp only [ToNat.toNat, h_4]
      apply Nat.mod_lt
      grind")]
pub const fn $euclid(a: $T, b: $T) -> $T
{
    ...
}
```
(Be careful with the indentation here! Lean is white-space sensitive!)

After running Hax again, `lake build` now says:
```
Build completed successfully (35 jobs).
```
Yay!

We are working on better automation for proofs like this one and on better coverage of the Rust core library, e.g., to be able to verify the binary gcd implementation in this crate as well.
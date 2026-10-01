# hax library

This crate contains helpers that can be used when writing Rust code that is proven
through the hax toolchain.

**⚠️ The code in this crate has no effect when compiled without `--cfg hax`. hax sets this cfg automatically when extracting a crate; a regular `cargo build` leaves it unset.**

## Main features

- `#[hax_lib::requires(...)]` and `#[hax_lib::ensures(...)]`: pre- and postconditions on functions.
- `#[hax_lib::attributes]`: enables `requires`/`ensures` on trait methods and refinements on struct fields.
- `hax_lib::loop_invariant!`: loop invariants.
- `Prop` and the logical operators `forall`, `exists`, `implies`: propositions beyond `bool`.
- `assume!`, `assert!`, `assert_prop!`: assumptions and assertions for the backends.
- `fstar!`, `coq!`, `proverif!`, ...: inline backend code.

## Example

```rust
/// The addition in `sum` does not overflow.
fn no_overflow(x: &[u32], y: &[u32]) -> hax_lib::Prop {
    hax_lib::forall(|i: usize| {
        hax_lib::implies(
            i < x.len(),
            x[i] as u64 + y[i] as u64 <= u32::MAX as u64,
        )
    })
}

#[hax_lib::requires(hax_lib::Prop::from(x.len() == y.len()) & no_overflow(&x, &y))]
#[hax_lib::ensures(|result| result.len() == x.len())]
fn sum(x: Vec<u32>, y: Vec<u32>) -> Vec<u32> {
    hax_lib::assert!(x.len() == y.len());
    hax_lib::assert_prop!(no_overflow(&x, &y));
    x.into_iter().zip(y).map(|(x, y)| x + y).collect()
}
```

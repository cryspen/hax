---
weight: 1
---

# Proving properties

In the last chapter, we proved one property on the `square` function:
panic freedom.

This contract stipulates that, given a small input, the function will
_return a value_: it will not panic or diverge. We could enrich the
contract of `square` with a post-condition about the fact it is an
increasing function:
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
  all_goals bv_decide")]
#[hax_lib::requires(x < 16)]
#[hax_lib::ensures(|res| res >= x)]
fn square(x: u8) -> u8 {
    x * x
}
```
This works as well (note that the proof script is slightly modified to apply `bv_decide` to all goals).

The property that we prove above demonstrates a very simple case of a proof using hax and Lean. For a more complex example, a version of the Barrett example is available in the 
[`examples`](https://github.com/cryspen/hax/tree/main/examples/lean_barrett) 
section of hax. 



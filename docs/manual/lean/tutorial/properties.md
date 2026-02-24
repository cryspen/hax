---
weight: 1
---

# Proving properties

In the previous chapter, we proved one property of the `square` function:
panic freedom.

This contract stipulates that, given a small input, the function will
_return a value_: it will not panic or diverge. We could enrich the
contract of `square` with a post-condition about the fact it is an
increasing function:
```{.rust .playable .lean-backend}
#[hax_lib::requires(x < 16)]
#[hax_lib::ensures(|res| res >= x)]
fn square(x: u8) -> u8 {
    x * x
}
```
This works as well.

The property that we prove above demonstrates a very simple case of a proof using hax and Lean. For a more complex example, a version of the Barrett example is available in the 
[`examples`](https://github.com/cryspen/hax/tree/main/examples/lean_barrett) 
section of hax. 



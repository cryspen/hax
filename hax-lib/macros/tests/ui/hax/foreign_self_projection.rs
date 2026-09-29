trait Super {
    type Item;
}

trait Sub: Super {
    fn id(&self, x: Self::Item) -> Self::Item;
}

struct S;

impl Super for S {
    type Item = u8;
}

#[hax_lib::attributes]
impl Sub for S {
    #[cfg_attr(all(), hax_lib::requires(true))]
    fn id(&self, x: Self::Item) -> Self::Item {
        x
    }
}

fn main() {}

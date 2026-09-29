#[hax_lib::attributes]
struct S {
    #[hax_lib::refine(x < 10)]
    #[cfg_attr(all(), hax_lib::refine(x < 5))]
    #[cfg_attr(all(), hax_lib::refine(x < 6))]
    x: u8,
    #[cfg_attr(any(), hax_lib::refine(y < 10))]
    #[hax_lib::refine(y < 5)]
    y: u8,
}

fn main() {}

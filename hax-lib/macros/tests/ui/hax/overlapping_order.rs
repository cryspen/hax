#[hax_lib::attributes]
struct S {
    #[hax_lib::order(0)]
    #[cfg_attr(all(), hax_lib::order(2))]
    x: u8,
    #[cfg_attr(any(), hax_lib::order(0))]
    #[hax_lib::order(1)]
    y: u8,
}

fn main() {}

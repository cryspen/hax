#[hax_lib::attributes]
struct S(u8, #[hax_lib::order(0)] u8);

#[hax_lib::attributes]
enum E {
    A(#[cfg_attr(all(), hax_lib::order(0))] u8),
}

fn main() {}

#[hax_lib::attributes]
struct S {
    #[hax_lib::order(99999999999)]
    x: u8,
    #[hax_lib::order(y)]
    y: u8,
}

fn main() {}

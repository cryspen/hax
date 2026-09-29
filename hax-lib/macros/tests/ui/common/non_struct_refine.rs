#[hax_lib::attributes]
enum E {
    A {
        #[cfg_attr(all(), hax_lib::refine(true))]
        a: u8,
    },
    B(#[hax_lib::refine(true)] u8),
}

#[hax_lib::attributes]
union U {
    #[hax_lib::refine(true)]
    u: u8,
}

#[hax_lib::attributes]
enum Disabled {
    A(#[cfg_attr(any(), hax_lib::refine(true))] u8),
}

fn main() {}

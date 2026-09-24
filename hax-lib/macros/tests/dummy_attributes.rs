//! Outside of hax, `#[hax_lib::attributes]` strips the hax attributes it
//! handles, including the ones behind an enabled `cfg_attr`. Run with
//! `RUSTFLAGS=""` to override the `--cfg hax` of `.cargo/config.toml`.
#![cfg(not(hax))]
#![allow(dead_code)]

#[hax_lib::attributes]
struct Refined {
    #[cfg_attr(all(), hax_lib::refine(x < 5), hax_lib::order(1))]
    #[cfg_attr(any(), hax_lib::refine(x < 6))]
    x: u8,
    #[hax_lib::refine(y > x)]
    #[hax_lib::order(0)]
    y: u8,
}

#[hax_lib::attributes]
struct Tuple(
    #[cfg_attr(all(), hax_lib::refine(true))] u8,
    #[hax_lib::order(0)] u8,
);

#[hax_lib::attributes]
enum Variants {
    Named {
        #[cfg_attr(all(), hax_lib::order(1))]
        a: u8,
        #[hax_lib::order(0)]
        b: u8,
    },
    Unnamed(#[cfg_attr(all(), hax_lib::order(0))] u8),
}

#[hax_lib::attributes]
impl Refined {
    #[cfg_attr(all(), hax_lib::requires(self.x < 5))]
    #[hax_lib::ensures(|result| result == self.x)]
    fn get(&self) -> u8 {
        self.x
    }
}

#[test]
fn stripped() {
    let r = Refined { x: 1, y: 2 };
    assert_eq!(r.get(), 1);
}

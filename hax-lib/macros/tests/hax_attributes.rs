//! Under `--cfg hax`, `#[hax_lib::attributes]` rewrites every hax attribute
//! behind a `cfg_attr`, and raises errors only for the enabled ones.
#![cfg(hax)]
#![allow(dead_code)]

#[hax_lib::attributes]
struct Refined {
    #[cfg_attr(hax_backend_fstar, hax_lib::refine(x < 5), hax_lib::order(1))]
    #[cfg_attr(hax_backend_lean, hax_lib::refine(x < 6), hax_lib::order(2))]
    x: u8,
    y: u8,
}

#[hax_lib::attributes]
struct DisabledError {
    #[cfg_attr(any(), hax_lib::order(99999999999))]
    #[cfg_attr(any(), hax_lib::refine(,))]
    x: u8,
}

trait Super {
    type Item;
}

trait Sub: Super {
    fn id(&self, x: Self::Item) -> Self::Item;
}

impl Super for Refined {
    type Item = u8;
}

/// `Self::Item` is not defined by this block (#2089): this only matters when
/// a specification is enabled.
#[hax_lib::attributes]
impl Sub for Refined {
    #[cfg_attr(any(), hax_lib::requires(x < 5))]
    fn id(&self, x: Self::Item) -> Self::Item {
        x
    }
}

#[test]
fn rewritten() {
    let r = Refined { x: 1, y: 2 };
    assert_eq!(r.id(r.x), 1);
}

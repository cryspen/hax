#[hax_lib::opaque]
#[hax_lib::requires(false)]
pub fn panic_explicit() -> ! {
    panic!()
}

#[hax_lib::opaque]
#[hax_lib::requires(false)]
pub fn panic(_msg: &str) -> ! {
    panic!()
}

#[hax_lib::opaque]
#[hax_lib::requires(false)]
pub fn panic_fmt(_fmt: super::fmt::Arguments) -> ! {
    panic!()
}

pub mod internal {
    // This module is used to break a dependency cycle (other core modules have
    // panics and this brings a dependency on core::fmt that we need to avoid)
    #[hax_lib::opaque]
    #[hax_lib::requires(false)]
    pub fn panic<T>() -> T {
        panic!("")
    }
}

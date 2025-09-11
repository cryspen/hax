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
    #[hax_lib::opaque]
    #[hax_lib::requires(false)]
    pub fn panic<T>() -> T {
        panic!()
    }
}

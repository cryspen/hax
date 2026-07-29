//! Hax attributes behind `cfg_attr`, so that `hax-lib` can be a
//! `cfg(hax)`-gated dependency. See issue #1496.
//! @off: ssprove, proverif, legacy-lean
#![allow(dead_code)]

struct Counter {
    n: usize,
}

#[cfg_attr(hax, hax_lib::attributes)]
impl Counter {
    #[cfg_attr(hax, hax_lib::requires(self.n < 5))]
    fn get(&self) -> usize {
        self.n
    }

    #[cfg_attr(hax, hax_lib::ensures(|result| result == self.n))]
    fn get_ensures(&self) -> usize {
        self.n
    }

    /// The `cfg_attr` predicate is preserved, not inlined: this
    /// precondition shows up in the F\* extraction only.
    #[cfg_attr(hax_backend_fstar, hax_lib::requires(self.n < 5))]
    fn get_fstar_only(&self) -> usize {
        self.n
    }

    /// A `cfg_attr` may carry several attributes: only the hax ones are
    /// rewritten.
    #[cfg_attr(hax, hax_lib::requires(self.n < 5), inline)]
    fn get_inline(&self) -> usize {
        self.n
    }
}

#[cfg_attr(hax, hax_lib::attributes)]
trait Double {
    #[cfg_attr(hax, hax_lib::requires(x < 100))]
    #[cfg_attr(hax, hax_lib::ensures(|result| result >= x))]
    fn double(&self, x: u8) -> u8;

    #[cfg_attr(hax_backend_fstar, hax_lib::requires(x < 100))]
    fn double_fstar_only(&self, x: u8) -> u8;
}

#[cfg_attr(hax, hax_lib::attributes)]
impl Double for Counter {
    #[cfg_attr(hax, hax_lib::requires(x < 100))]
    #[cfg_attr(hax, hax_lib::ensures(|result| result >= x))]
    fn double(&self, x: u8) -> u8 {
        x + x
    }

    #[cfg_attr(hax_backend_fstar, hax_lib::requires(x < 100))]
    fn double_fstar_only(&self, x: u8) -> u8 {
        x + x
    }
}

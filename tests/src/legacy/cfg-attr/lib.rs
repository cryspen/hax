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

#[cfg_attr(hax, hax_lib::attributes)]
struct Refined<const LEN: usize> {
    #[cfg_attr(hax, hax_lib::refine(hax_lib::forall(|i: usize| hax_lib::implies(
        i < indices.len(),
        (indices[i] as usize) < 2
    ))))]
    indices: [u8; LEN],
    #[cfg_attr(hax_backend_fstar, hax_lib::refine(x < 5))]
    x: u8,
}

#[cfg_attr(hax, hax_lib::attributes)]
struct Reordered {
    x: u8,
    #[cfg_attr(hax, hax_lib::order(-1))]
    y: u8,
}

/// One refinement per backend: each backend only sees its own.
#[cfg_attr(hax, hax_lib::attributes)]
struct PerBackendRefined {
    #[cfg_attr(hax_backend_fstar, hax_lib::refine(x < 5))]
    #[cfg_attr(hax_backend_coq, hax_lib::refine(x < 6))]
    x: u8,
}

/// One field order per backend: `y` comes first in F\*, last in Coq.
#[cfg_attr(hax, hax_lib::attributes)]
struct PerBackendReordered {
    x: u8,
    #[cfg_attr(hax_backend_fstar, hax_lib::order(-1))]
    #[cfg_attr(hax_backend_coq, hax_lib::order(5))]
    y: u8,
    z: u8,
}

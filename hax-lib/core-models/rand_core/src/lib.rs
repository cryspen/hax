#![allow(unused)]
// `coverage(off)` is unstable; `cfg(coverage_nightly)` is set only by
// `cargo llvm-cov`, so normal builds and extraction never see this.
#![cfg_attr(coverage_nightly, feature(coverage_attribute))]

#[hax_lib::attributes]
pub trait RngCore {
    // Required methods
    #[hax_lib::requires(true)]
    fn next_u32(&mut self) -> u32;
    #[hax_lib::requires(true)]
    fn next_u64(&mut self) -> u64;
    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|_| future(dst).len() == dst.len())]
    fn fill_bytes(&mut self, dst: &mut [u8]);
}

pub trait CryptoRng: RngCore {}

mod os {
    pub struct OsRng;
    // Dummy impl
    #[hax_lib::opaque]
    impl super::RngCore for OsRng {
        // Excluded from coverage: the model has no source of randomness, so
        // these are dummies and the constants below are not behaviour a test
        // could pin. `mutants::skip` for the same reason: no test can tell one
        // dummy constant from another.
        #[cfg_attr(coverage_nightly, coverage(off))]
        #[cfg_attr(test, mutants::skip)]
        fn next_u32(&mut self) -> u32 {
            0
        }
        // Excluded from coverage and mutation, as `next_u32`.
        #[cfg_attr(coverage_nightly, coverage(off))]
        #[cfg_attr(test, mutants::skip)]
        fn next_u64(&mut self) -> u64 {
            0
        }
        // Excluded from coverage and mutation, as `next_u32`.
        #[cfg_attr(coverage_nightly, coverage(off))]
        #[cfg_attr(test, mutants::skip)]
        fn fill_bytes(&mut self, dst: &mut [u8]) {}
    }
    impl super::CryptoRng for OsRng {}
}

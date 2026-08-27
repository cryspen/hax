#![allow(unused)]
// `coverage(off)` is unstable; `cfg(coverage_nightly)` is set only by
// `cargo llvm-cov`, so normal builds and extraction never see this.
#![cfg_attr(coverage_nightly, feature(coverage_attribute))]

pub trait RngCore {
    // Required methods
    fn next_u32(&mut self) -> u32;
    fn next_u64(&mut self) -> u64;
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
        // could pin.
        #[cfg_attr(coverage_nightly, coverage(off))]
        fn next_u32(&mut self) -> u32 {
            0
        }
        // Excluded from coverage: a dummy, as `next_u32`.
        #[cfg_attr(coverage_nightly, coverage(off))]
        fn next_u64(&mut self) -> u64 {
            0
        }
        // Excluded from coverage: a dummy, as `next_u32`.
        #[cfg_attr(coverage_nightly, coverage(off))]
        fn fill_bytes(&mut self, dst: &mut [u8]) {}
    }
    impl super::CryptoRng for OsRng {}
}

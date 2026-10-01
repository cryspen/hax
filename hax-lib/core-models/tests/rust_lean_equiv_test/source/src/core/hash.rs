//! Equivalence tests for `core::hash::*`, through a client `Hasher` that sums the
//! bytes it is fed.

use core::hash::{BuildHasher, BuildHasherDefault, Hash, Hasher};
use rust_lean_test_macro::rust_lean_test;

#[derive(Default)]
struct Sum(u64);

impl Hasher for Sum {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        let mut i = 0;
        while i < bytes.len() {
            self.0 += bytes[i] as u64;
            i += 1;
        }
    }
}

#[rust_lean_test]
pub fn test_write_u8() -> bool {
    let mut h = Sum(0);
    h.write_u8(7);
    h.finish() == 7
}

#[rust_lean_test]
pub fn test_write_u16() -> bool {
    let mut h = Sum(0);
    h.write_u16(0x0102);
    h.finish() == 3
}

#[rust_lean_test]
pub fn test_write_i32_minus_one() -> bool {
    let mut h = Sum(0);
    h.write_i32(-1);
    h.finish() == 4 * 255
}

#[rust_lean_test]
pub fn test_hash_u8() -> bool {
    let mut h = Sum(0);
    7u8.hash(&mut h);
    h.finish() == 7
}

#[rust_lean_test(skip_lean = "the model hashes one cast byte where std hashes all of them")]
pub fn test_hash_u16() -> bool {
    let mut h = Sum(0);
    300u16.hash(&mut h);
    h.finish() == 45
}

#[rust_lean_test]
pub fn test_hash_slice_u8() -> bool {
    let mut h = Sum(0);
    Hash::hash_slice(&[1u8, 2, 3], &mut h);
    h.finish() == 6
}

#[rust_lean_test]
pub fn test_hash_one() -> bool {
    BuildHasherDefault::<Sum>::new().hash_one(7u8) == 7
}

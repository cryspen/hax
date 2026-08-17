//! Equivalence tests for `core::hash::*`.
//!
//! Every test in this file is commented out, for a single structural reason:
//! the model's `Hash::hash` deviates from `core`'s in *arity*. `core` threads
//! the hasher by mutable reference,
//!
//! ```ignore
//! fn hash<H: Hasher>(&self, state: &mut H);
//! ```
//!
//! while the model threads it by value (`fn hash<H: Hasher>(&self, h: H) -> H`),
//! as it does everywhere else. A `#[rust_lean_test]` body calls **real** `core`,
//! so any `Hash::hash` / `Hash::hash_slice` / `BuildHasher::hash_one` call site
//! extracts against the real signature and cannot be applied to the model's
//! trait — the Lean side does not elaborate, so `skip_lean` cannot rescue it
//! either (see the "Skipping the Lean half" section of the core-models README).
//!
//! Reaching a `Hasher` at all has the same problem from the other end: the only
//! concrete `Hasher`s `core`/`std` expose are `DefaultHasher`, `SipHasher13` and
//! the deprecated `SipHasher`, none of which the model provides, and a hasher
//! defined here would have to spell out all sixteen `Hasher` methods by hand
//! (the model has no trait defaults) before it lined up with the model's trait.
//!
//! What the model *is* checked against lives in the `#[cfg(test)]` block of
//! `core-models/src/core/hash.rs`: a byte-log hasher implemented twice over —
//! once for the model's `Hasher` and once for `std::hash::Hasher` — which pins
//! each `write_*` method, `hash`/`hash_slice` at the widths where the model does
//! not deviate, and `BuildHasherDefault` + `BuildHasher::hash_one`, against real
//! std.
//!
//! TODO(hash-hasher-arity): once the model's `Hash::hash` takes `&mut H` (or the
//! extraction learns to bridge the two calling conventions), turn the tests
//! below back on.

// ----- Hasher::write / Hasher::write_* / Hasher::finish -----------------------
//
// use rust_lean_test_macro::rust_lean_test;
//
// pub struct Xor(u64);
//
// impl core::hash::Hasher for Xor {
//     fn finish(&self) -> u64 {
//         self.0
//     }
//     fn write(&mut self, bytes: &[u8]) {
//         let mut i = 0;
//         while i < bytes.len() {
//             self.0 = self.0 ^ (bytes[i] as u64);
//             i += 1;
//         }
//     }
//     // ... and the thirteen other `write_*` methods, which the model requires
//     // an implementation to provide.
// }
//
// #[rust_lean_test]
// pub fn test_hasher_write_u8_zero() -> bool {
//     let mut h = Xor(0);
//     core::hash::Hasher::write_u8(&mut h, 0);
//     core::hash::Hasher::finish(&h) == 0
// }
//
// #[rust_lean_test]
// pub fn test_hasher_write_u8_max() -> bool {
//     let mut h = Xor(0);
//     core::hash::Hasher::write_u8(&mut h, u8::MAX);
//     core::hash::Hasher::finish(&h) == u8::MAX as u64
// }

// ----- Hash::hash / Hash::hash_slice -----------------------------------------
//
// #[rust_lean_test]
// pub fn test_hash_u8() -> bool {
//     let mut h = Xor(0);
//     core::hash::Hash::hash(&7u8, &mut h);
//     core::hash::Hasher::finish(&h) == 7
// }
//
// #[rust_lean_test]
// pub fn test_hash_slice_empty() -> bool {
//     let mut h = Xor(0);
//     core::hash::Hash::hash_slice(&[] as &[u8], &mut h);
//     core::hash::Hasher::finish(&h) == 0
// }

// ----- BuildHasher / BuildHasherDefault --------------------------------------
//
// #[rust_lean_test]
// pub fn test_build_hasher_default_hash_one() -> bool {
//     let bh = core::hash::BuildHasherDefault::<Xor>::new();
//     core::hash::BuildHasher::hash_one(&bh, 7u8) == 7
// }

// ----- SipHasher (not modeled) ------------------------------------------------
//
// `core::hash::SipHasher` is deprecated in std and its `Hasher` output is
// explicitly not guaranteed stable, so there is nothing a test could pin it
// against. The model does not provide it.

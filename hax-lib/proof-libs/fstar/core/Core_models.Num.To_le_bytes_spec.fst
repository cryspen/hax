module Core_models.Num.To_le_bytes_spec

/// Behavioural contract of the `to_le_bytes` integer models, which extract the
/// bytes with shifts rather than routing through a primitive.
///
/// Every lemma here is a proof obligation, not runtime code: the file exists so
/// that a `to_le_bytes` model whose bytes consumers cannot name is a build
/// failure rather than a silently unusable model.

open FStar.Mul
open Rust_primitives

#push-options "--fuel 0 --ifuel 1 --z3rlimit 50"

/// Byte `b` of the little-endian encoding is `(x >> 8b) mod 256`.
let to_le_bytes_u64_index (x: u64) (b: nat{b < 8})
    : Lemma
      (ensures
        v (Seq.index (Core_models.Num.impl_u64__to_le_bytes x) b) == (v x / pow2 (8 * b)) % pow2 8)
  = assert_norm (pow2 8 == 256)

let to_le_bytes_u32_index (x: u32) (b: nat{b < 4})
    : Lemma
      (ensures
        v (Seq.index (Core_models.Num.impl_u32__to_le_bytes x) b) == (v x / pow2 (8 * b)) % pow2 8)
  = assert_norm (pow2 8 == 256)

let to_le_bytes_u16_index (x: u16) (b: nat{b < 2})
    : Lemma
      (ensures
        v (Seq.index (Core_models.Num.impl_u16__to_le_bytes x) b) == (v x / pow2 (8 * b)) % pow2 8)
  = assert_norm (pow2 8 == 256)

/// A single-byte type is its own only byte.
let to_le_bytes_u8_index (x: u8)
    : Lemma (ensures Seq.index (Core_models.Num.impl_u8__to_le_bytes x) 0 == x)
  = assert_norm (pow2 8 == 256)

#pop-options

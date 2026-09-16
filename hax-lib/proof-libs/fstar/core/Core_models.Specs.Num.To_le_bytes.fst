module Core_models.Specs.Num.To_le_bytes

/// Byte `b` of a `to_le_bytes` model is `(x >> 8b) mod 256`.

open FStar.Mul
open Rust_primitives

#push-options "--fuel 0 --ifuel 1 --z3rlimit 50"

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

module Core_models.Num.Checked_mul_spec

/// Behavioural contract of the `checked_mul` integer models, which route
/// through `Rust_primitives.Integers.mul_overflow`.
///
/// Every lemma here is a proof obligation, not runtime code: the file exists
/// so that a mis-stated overflow condition is a build failure rather than a
/// model that silently reports overflow on correct multiplications.

open Rust_primitives

/// unsigned — in range
let checked_mul_u64_some (x y: u64) : Lemma
  (requires v x * v y <= maxint U64)
  (ensures Core_models.Num.impl_u64__checked_mul x y
           == Core_models.Option.Option_Some (x *! y))
  = ()

/// unsigned — overflow
let checked_mul_u64_none (x y: u64) : Lemma
  (requires v x * v y > maxint U64)
  (ensures Core_models.Num.impl_u64__checked_mul x y
           == Core_models.Option.Option_None)
  = ()

/// signed — in range, including negative products
let checked_mul_i32_some (x y: i32) : Lemma
  (requires v x * v y <= maxint I32 /\ v x * v y >= minint I32)
  (ensures Core_models.Num.impl_i32__checked_mul x y
           == Core_models.Option.Option_Some (x *! y))
  = ()

/// signed — underflow
let checked_mul_i32_none (x y: i32) : Lemma
  (requires v x * v y < minint I32)
  (ensures Core_models.Num.impl_i32__checked_mul x y
           == Core_models.Option.Option_None)
  = ()

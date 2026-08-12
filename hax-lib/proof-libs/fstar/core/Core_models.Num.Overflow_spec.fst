module Core_models.Num.Overflow_spec

/// Behavioural contract of the `checked_*` integer models, which route
/// through `Rust_primitives.Arithmetic.overflowing_{add,sub}_*`.
///
/// Every lemma here is a proof obligation, not runtime code: the file exists
/// so that leaving one of those primitives uninterpreted is a build failure
/// rather than a silently unusable model (#2127).

open FStar.Mul
open Rust_primitives

/// unsigned add — in range
let checked_add_u64_some (x y: u64) : Lemma
  (requires v x + v y <= maxint U64)
  (ensures Core_models.Num.impl_u64__checked_add x y
           == Core_models.Option.Option_Some (x +! y))
  = ()

/// unsigned add — overflow
let checked_add_u64_none (x y: u64) : Lemma
  (requires v x + v y > maxint U64)
  (ensures Core_models.Num.impl_u64__checked_add x y
           == Core_models.Option.Option_None)
  = ()

/// signed add — in range
let checked_add_i32_some (x y: i32) : Lemma
  (requires v x + v y <= maxint I32 /\ v x + v y >= minint I32)
  (ensures Core_models.Num.impl_i32__checked_add x y
           == Core_models.Option.Option_Some (x +! y))
  = ()

/// signed sub — in range
let checked_sub_i32_some (x y: i32) : Lemma
  (requires v x - v y <= maxint I32 /\ v x - v y >= minint I32)
  (ensures Core_models.Num.impl_i32__checked_sub x y
           == Core_models.Option.Option_Some (x -! y))
  = ()

/// signed sub — underflow
let checked_sub_i32_none (x y: i32) : Lemma
  (requires v x - v y < minint I32)
  (ensures Core_models.Num.impl_i32__checked_sub x y
           == Core_models.Option.Option_None)
  = ()

/// unsigned sub already had a definition — guard against regressing it
let checked_sub_u64_some (x y: u64) : Lemma
  (requires v y <= v x)
  (ensures Core_models.Num.impl_u64__checked_sub x y
           == Core_models.Option.Option_Some (x -! y))
  = ()

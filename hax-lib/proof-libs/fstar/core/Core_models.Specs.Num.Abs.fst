module Core_models.Specs.Num.Abs

/// The `abs` models agree with `Rust_primitives.Integers.abs_int` on the domain
/// their `requires` carves out.

open FStar.Mul
open Rust_primitives

let abs_i8 (x: i8) : Lemma
  (requires v x > minint I8)
  (ensures Core_models.Num.impl_i8__abs x == abs_int x)
  = ()

let abs_i16 (x: i16) : Lemma
  (requires v x > minint I16)
  (ensures Core_models.Num.impl_i16__abs x == abs_int x)
  = ()

let abs_i32 (x: i32) : Lemma
  (requires v x > minint I32)
  (ensures Core_models.Num.impl_i32__abs x == abs_int x)
  = ()

let abs_i64 (x: i64) : Lemma
  (requires v x > minint I64)
  (ensures Core_models.Num.impl_i64__abs x == abs_int x)
  = ()

let abs_i128 (x: i128) : Lemma
  (requires v x > minint I128)
  (ensures Core_models.Num.impl_i128__abs x == abs_int x)
  = ()

let abs_isize (x: isize) : Lemma
  (requires v x > minint ISIZE)
  (ensures Core_models.Num.impl_isize__abs x == abs_int x)
  = ()

let abs_i16_v (x: i16) : Lemma
  (requires v x > minint I16)
  (ensures v (Core_models.Num.impl_i16__abs x) == (if v x < 0 then - (v x) else v x))
  = ()

let abs_i32_v (x: i32) : Lemma
  (requires v x > minint I32)
  (ensures v (Core_models.Num.impl_i32__abs x) == (if v x < 0 then - (v x) else v x))
  = ()

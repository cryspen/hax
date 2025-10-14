module Core_models.Num
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

let impl_u8__MIN: u8 = mk_u8 0

let impl_u8__MAX: u8 = mk_u8 255

let impl_u8__BITS: u32 = mk_u32 8

val impl_u8__wrapping_add (x y: u8) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val impl_u8__saturating_add (x y: u8) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val impl_u8__overflowing_add (x y: u8) : Prims.Pure (u8 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_u8__wrapping_sub (x y: u8) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val impl_u8__saturating_sub (x y: u8) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val impl_u8__overflowing_sub (x y: u8) : Prims.Pure (u8 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_u8__wrapping_mul (x y: u8) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val impl_u8__saturating_mul (x y: u8) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val impl_u8__overflowing_mul (x y: u8) : Prims.Pure (u8 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_u8__pow (x: u8) (exp: u32) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val impl_u8__count_ones (x: u8) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u8__rotate_right (x: u8) (n: u32) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val impl_u8__rotate_left (x: u8) (n: u32) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val impl_u8__leading_zeros (x: u8) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u8__ilog2 (x: u8) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u8__from_str_radix (src: string) (radix: u32)
    : Prims.Pure (Core_models.Result.t_Result u8 Core_models.Num.Error.t_ParseIntError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_u8__from_be_bytes (bytes: t_Array u8 (mk_usize 1))
    : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val impl_u8__from_le_bytes (bytes: t_Array u8 (mk_usize 1))
    : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

val impl_u8__to_be_bytes (bytes: u8)
    : Prims.Pure (t_Array u8 (mk_usize 1)) Prims.l_True (fun _ -> Prims.l_True)

val impl_u8__to_le_bytes (bytes: u8)
    : Prims.Pure (t_Array u8 (mk_usize 1)) Prims.l_True (fun _ -> Prims.l_True)

val impl_u8__rem_euclid (x y: u8) : Prims.Pure u8 (requires y <>. mk_u8 0) (fun _ -> Prims.l_True)

let impl_u16__MIN: u16 = mk_u16 0

let impl_u16__MAX: u16 = mk_u16 65535

let impl_u16__BITS: u32 = mk_u32 16

val impl_u16__wrapping_add (x y: u16) : Prims.Pure u16 Prims.l_True (fun _ -> Prims.l_True)

val impl_u16__saturating_add (x y: u16) : Prims.Pure u16 Prims.l_True (fun _ -> Prims.l_True)

val impl_u16__overflowing_add (x y: u16)
    : Prims.Pure (u16 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_u16__wrapping_sub (x y: u16) : Prims.Pure u16 Prims.l_True (fun _ -> Prims.l_True)

val impl_u16__saturating_sub (x y: u16) : Prims.Pure u16 Prims.l_True (fun _ -> Prims.l_True)

val impl_u16__overflowing_sub (x y: u16)
    : Prims.Pure (u16 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_u16__wrapping_mul (x y: u16) : Prims.Pure u16 Prims.l_True (fun _ -> Prims.l_True)

val impl_u16__saturating_mul (x y: u16) : Prims.Pure u16 Prims.l_True (fun _ -> Prims.l_True)

val impl_u16__overflowing_mul (x y: u16)
    : Prims.Pure (u16 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_u16__pow (x: u16) (exp: u32) : Prims.Pure u16 Prims.l_True (fun _ -> Prims.l_True)

val impl_u16__count_ones (x: u16) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u16__rotate_right (x: u16) (n: u32) : Prims.Pure u16 Prims.l_True (fun _ -> Prims.l_True)

val impl_u16__rotate_left (x: u16) (n: u32) : Prims.Pure u16 Prims.l_True (fun _ -> Prims.l_True)

val impl_u16__leading_zeros (x: u16) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u16__ilog2 (x: u16) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u16__from_str_radix (src: string) (radix: u32)
    : Prims.Pure (Core_models.Result.t_Result u16 Core_models.Num.Error.t_ParseIntError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_u16__from_be_bytes (bytes: t_Array u16 (mk_usize 2))
    : Prims.Pure u16 Prims.l_True (fun _ -> Prims.l_True)

val impl_u16__from_le_bytes (bytes: t_Array u16 (mk_usize 2))
    : Prims.Pure u16 Prims.l_True (fun _ -> Prims.l_True)

val impl_u16__to_be_bytes (bytes: u16)
    : Prims.Pure (t_Array u16 (mk_usize 2)) Prims.l_True (fun _ -> Prims.l_True)

val impl_u16__to_le_bytes (bytes: u16)
    : Prims.Pure (t_Array u16 (mk_usize 2)) Prims.l_True (fun _ -> Prims.l_True)

val impl_u16__rem_euclid (x y: u16)
    : Prims.Pure u16 (requires y <>. mk_u16 0) (fun _ -> Prims.l_True)

let impl_u32__MIN: u32 = mk_u32 0

let impl_u32__MAX: u32 = mk_u32 4294967295

let impl_u32__BITS: u32 = mk_u32 32

val impl_u32__wrapping_add (x y: u32) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u32__saturating_add (x y: u32) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u32__overflowing_add (x y: u32)
    : Prims.Pure (u32 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_u32__wrapping_sub (x y: u32) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u32__saturating_sub (x y: u32) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u32__overflowing_sub (x y: u32)
    : Prims.Pure (u32 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_u32__wrapping_mul (x y: u32) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u32__saturating_mul (x y: u32) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u32__overflowing_mul (x y: u32)
    : Prims.Pure (u32 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_u32__pow (x exp: u32) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u32__count_ones (x: u32) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u32__rotate_right (x n: u32) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u32__rotate_left (x n: u32) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u32__leading_zeros (x: u32) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u32__ilog2 (x: u32) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u32__from_str_radix (src: string) (radix: u32)
    : Prims.Pure (Core_models.Result.t_Result u32 Core_models.Num.Error.t_ParseIntError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_u32__from_be_bytes (bytes: t_Array u32 (mk_usize 4))
    : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u32__from_le_bytes (bytes: t_Array u32 (mk_usize 4))
    : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u32__to_be_bytes (bytes: u32)
    : Prims.Pure (t_Array u32 (mk_usize 4)) Prims.l_True (fun _ -> Prims.l_True)

val impl_u32__to_le_bytes (bytes: u32)
    : Prims.Pure (t_Array u32 (mk_usize 4)) Prims.l_True (fun _ -> Prims.l_True)

val impl_u32__rem_euclid (x y: u32)
    : Prims.Pure u32 (requires y <>. mk_u32 0) (fun _ -> Prims.l_True)

let impl_u64__MIN: u64 = mk_u64 0

let impl_u64__MAX: u64 = mk_u64 18446744073709551615

let impl_u64__BITS: u32 = mk_u32 64

val impl_u64__wrapping_add (x y: u64) : Prims.Pure u64 Prims.l_True (fun _ -> Prims.l_True)

val impl_u64__saturating_add (x y: u64) : Prims.Pure u64 Prims.l_True (fun _ -> Prims.l_True)

val impl_u64__overflowing_add (x y: u64)
    : Prims.Pure (u64 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_u64__wrapping_sub (x y: u64) : Prims.Pure u64 Prims.l_True (fun _ -> Prims.l_True)

val impl_u64__saturating_sub (x y: u64) : Prims.Pure u64 Prims.l_True (fun _ -> Prims.l_True)

val impl_u64__overflowing_sub (x y: u64)
    : Prims.Pure (u64 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_u64__wrapping_mul (x y: u64) : Prims.Pure u64 Prims.l_True (fun _ -> Prims.l_True)

val impl_u64__saturating_mul (x y: u64) : Prims.Pure u64 Prims.l_True (fun _ -> Prims.l_True)

val impl_u64__overflowing_mul (x y: u64)
    : Prims.Pure (u64 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_u64__pow (x: u64) (exp: u32) : Prims.Pure u64 Prims.l_True (fun _ -> Prims.l_True)

val impl_u64__count_ones (x: u64) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u64__rotate_right (x: u64) (n: u32) : Prims.Pure u64 Prims.l_True (fun _ -> Prims.l_True)

val impl_u64__rotate_left (x: u64) (n: u32) : Prims.Pure u64 Prims.l_True (fun _ -> Prims.l_True)

val impl_u64__leading_zeros (x: u64) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u64__ilog2 (x: u64) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u64__from_str_radix (src: string) (radix: u32)
    : Prims.Pure (Core_models.Result.t_Result u64 Core_models.Num.Error.t_ParseIntError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_u64__from_be_bytes (bytes: t_Array u64 (mk_usize 8))
    : Prims.Pure u64 Prims.l_True (fun _ -> Prims.l_True)

val impl_u64__from_le_bytes (bytes: t_Array u64 (mk_usize 8))
    : Prims.Pure u64 Prims.l_True (fun _ -> Prims.l_True)

val impl_u64__to_be_bytes (bytes: u64)
    : Prims.Pure (t_Array u64 (mk_usize 8)) Prims.l_True (fun _ -> Prims.l_True)

val impl_u64__to_le_bytes (bytes: u64)
    : Prims.Pure (t_Array u64 (mk_usize 8)) Prims.l_True (fun _ -> Prims.l_True)

val impl_u64__rem_euclid (x y: u64)
    : Prims.Pure u64 (requires y <>. mk_u64 0) (fun _ -> Prims.l_True)

let impl_u128__MIN: u128 = mk_u128 0

let impl_u128__MAX: u128 = mk_u128 340282366920938463463374607431768211455

let impl_u128__BITS: u32 = mk_u32 128

val impl_u128__wrapping_add (x y: u128) : Prims.Pure u128 Prims.l_True (fun _ -> Prims.l_True)

val impl_u128__saturating_add (x y: u128) : Prims.Pure u128 Prims.l_True (fun _ -> Prims.l_True)

val impl_u128__overflowing_add (x y: u128)
    : Prims.Pure (u128 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_u128__wrapping_sub (x y: u128) : Prims.Pure u128 Prims.l_True (fun _ -> Prims.l_True)

val impl_u128__saturating_sub (x y: u128) : Prims.Pure u128 Prims.l_True (fun _ -> Prims.l_True)

val impl_u128__overflowing_sub (x y: u128)
    : Prims.Pure (u128 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_u128__wrapping_mul (x y: u128) : Prims.Pure u128 Prims.l_True (fun _ -> Prims.l_True)

val impl_u128__saturating_mul (x y: u128) : Prims.Pure u128 Prims.l_True (fun _ -> Prims.l_True)

val impl_u128__overflowing_mul (x y: u128)
    : Prims.Pure (u128 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_u128__pow (x: u128) (exp: u32) : Prims.Pure u128 Prims.l_True (fun _ -> Prims.l_True)

val impl_u128__count_ones (x: u128) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u128__rotate_right (x: u128) (n: u32)
    : Prims.Pure u128 Prims.l_True (fun _ -> Prims.l_True)

val impl_u128__rotate_left (x: u128) (n: u32) : Prims.Pure u128 Prims.l_True (fun _ -> Prims.l_True)

val impl_u128__leading_zeros (x: u128) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u128__ilog2 (x: u128) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_u128__from_str_radix (src: string) (radix: u32)
    : Prims.Pure (Core_models.Result.t_Result u128 Core_models.Num.Error.t_ParseIntError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_u128__from_be_bytes (bytes: t_Array u128 (mk_usize 16))
    : Prims.Pure u128 Prims.l_True (fun _ -> Prims.l_True)

val impl_u128__from_le_bytes (bytes: t_Array u128 (mk_usize 16))
    : Prims.Pure u128 Prims.l_True (fun _ -> Prims.l_True)

val impl_u128__to_be_bytes (bytes: u128)
    : Prims.Pure (t_Array u128 (mk_usize 16)) Prims.l_True (fun _ -> Prims.l_True)

val impl_u128__to_le_bytes (bytes: u128)
    : Prims.Pure (t_Array u128 (mk_usize 16)) Prims.l_True (fun _ -> Prims.l_True)

val impl_u128__rem_euclid (x y: u128)
    : Prims.Pure u128 (requires y <>. mk_u128 0) (fun _ -> Prims.l_True)

let impl_usize__MIN: usize = mk_usize 0

let impl_usize__MAX: usize = Rust_primitives.Arithmetic.v_USIZE_MAX

let impl_usize__BITS: u32 = Rust_primitives.Arithmetic.v_SIZE_BITS

val impl_usize__wrapping_add (x y: usize) : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val impl_usize__saturating_add (x y: usize) : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val impl_usize__overflowing_add (x y: usize)
    : Prims.Pure (usize & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_usize__wrapping_sub (x y: usize) : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val impl_usize__saturating_sub (x y: usize) : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val impl_usize__overflowing_sub (x y: usize)
    : Prims.Pure (usize & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_usize__wrapping_mul (x y: usize) : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val impl_usize__saturating_mul (x y: usize) : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val impl_usize__overflowing_mul (x y: usize)
    : Prims.Pure (usize & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_usize__pow (x: usize) (exp: u32) : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val impl_usize__count_ones (x: usize) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_usize__rotate_right (x: usize) (n: u32)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val impl_usize__rotate_left (x: usize) (n: u32)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val impl_usize__leading_zeros (x: usize) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_usize__ilog2 (x: usize) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_usize__from_str_radix (src: string) (radix: u32)
    : Prims.Pure (Core_models.Result.t_Result usize Core_models.Num.Error.t_ParseIntError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_usize__from_be_bytes (bytes: t_Array usize (mk_usize 0))
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val impl_usize__from_le_bytes (bytes: t_Array usize (mk_usize 0))
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val impl_usize__to_be_bytes (bytes: usize)
    : Prims.Pure (t_Array usize (mk_usize 0)) Prims.l_True (fun _ -> Prims.l_True)

val impl_usize__to_le_bytes (bytes: usize)
    : Prims.Pure (t_Array usize (mk_usize 0)) Prims.l_True (fun _ -> Prims.l_True)

val impl_usize__rem_euclid (x y: usize)
    : Prims.Pure usize (requires y <>. mk_usize 0) (fun _ -> Prims.l_True)

let impl_i8__MIN: i8 = mk_i8 (-128)

let impl_i8__MAX: i8 = mk_i8 127

let impl_i8__BITS: u32 = mk_u32 8

val impl_i8__wrapping_add (x y: i8) : Prims.Pure i8 Prims.l_True (fun _ -> Prims.l_True)

val impl_i8__saturating_add (x y: i8) : Prims.Pure i8 Prims.l_True (fun _ -> Prims.l_True)

val impl_i8__overflowing_add (x y: i8) : Prims.Pure (i8 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_i8__wrapping_sub (x y: i8) : Prims.Pure i8 Prims.l_True (fun _ -> Prims.l_True)

val impl_i8__saturating_sub (x y: i8) : Prims.Pure i8 Prims.l_True (fun _ -> Prims.l_True)

val impl_i8__overflowing_sub (x y: i8) : Prims.Pure (i8 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_i8__wrapping_mul (x y: i8) : Prims.Pure i8 Prims.l_True (fun _ -> Prims.l_True)

val impl_i8__saturating_mul (x y: i8) : Prims.Pure i8 Prims.l_True (fun _ -> Prims.l_True)

val impl_i8__overflowing_mul (x y: i8) : Prims.Pure (i8 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_i8__pow (x: i8) (exp: u32) : Prims.Pure i8 Prims.l_True (fun _ -> Prims.l_True)

val impl_i8__count_ones (x: i8) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i8__rotate_right (x: i8) (n: u32) : Prims.Pure i8 Prims.l_True (fun _ -> Prims.l_True)

val impl_i8__rotate_left (x: i8) (n: u32) : Prims.Pure i8 Prims.l_True (fun _ -> Prims.l_True)

val impl_i8__leading_zeros (x: i8) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i8__ilog2 (x: i8) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i8__from_str_radix (src: string) (radix: u32)
    : Prims.Pure (Core_models.Result.t_Result i8 Core_models.Num.Error.t_ParseIntError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_i8__from_be_bytes (bytes: t_Array i8 (mk_usize 1))
    : Prims.Pure i8 Prims.l_True (fun _ -> Prims.l_True)

val impl_i8__from_le_bytes (bytes: t_Array i8 (mk_usize 1))
    : Prims.Pure i8 Prims.l_True (fun _ -> Prims.l_True)

val impl_i8__to_be_bytes (bytes: i8)
    : Prims.Pure (t_Array i8 (mk_usize 1)) Prims.l_True (fun _ -> Prims.l_True)

val impl_i8__to_le_bytes (bytes: i8)
    : Prims.Pure (t_Array i8 (mk_usize 1)) Prims.l_True (fun _ -> Prims.l_True)

val impl_i8__rem_euclid (x y: i8) : Prims.Pure i8 (requires y <>. mk_i8 0) (fun _ -> Prims.l_True)

val impl_i8__abs (x: i8) : Prims.Pure i8 (requires x >. impl_i8__MIN) (fun _ -> Prims.l_True)

let impl_i16__MIN: i16 = mk_i16 (-32768)

let impl_i16__MAX: i16 = mk_i16 32767

let impl_i16__BITS: u32 = mk_u32 16

val impl_i16__wrapping_add (x y: i16) : Prims.Pure i16 Prims.l_True (fun _ -> Prims.l_True)

val impl_i16__saturating_add (x y: i16) : Prims.Pure i16 Prims.l_True (fun _ -> Prims.l_True)

val impl_i16__overflowing_add (x y: i16)
    : Prims.Pure (i16 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_i16__wrapping_sub (x y: i16) : Prims.Pure i16 Prims.l_True (fun _ -> Prims.l_True)

val impl_i16__saturating_sub (x y: i16) : Prims.Pure i16 Prims.l_True (fun _ -> Prims.l_True)

val impl_i16__overflowing_sub (x y: i16)
    : Prims.Pure (i16 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_i16__wrapping_mul (x y: i16) : Prims.Pure i16 Prims.l_True (fun _ -> Prims.l_True)

val impl_i16__saturating_mul (x y: i16) : Prims.Pure i16 Prims.l_True (fun _ -> Prims.l_True)

val impl_i16__overflowing_mul (x y: i16)
    : Prims.Pure (i16 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_i16__pow (x: i16) (exp: u32) : Prims.Pure i16 Prims.l_True (fun _ -> Prims.l_True)

val impl_i16__count_ones (x: i16) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i16__rotate_right (x: i16) (n: u32) : Prims.Pure i16 Prims.l_True (fun _ -> Prims.l_True)

val impl_i16__rotate_left (x: i16) (n: u32) : Prims.Pure i16 Prims.l_True (fun _ -> Prims.l_True)

val impl_i16__leading_zeros (x: i16) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i16__ilog2 (x: i16) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i16__from_str_radix (src: string) (radix: u32)
    : Prims.Pure (Core_models.Result.t_Result i16 Core_models.Num.Error.t_ParseIntError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_i16__from_be_bytes (bytes: t_Array i16 (mk_usize 2))
    : Prims.Pure i16 Prims.l_True (fun _ -> Prims.l_True)

val impl_i16__from_le_bytes (bytes: t_Array i16 (mk_usize 2))
    : Prims.Pure i16 Prims.l_True (fun _ -> Prims.l_True)

val impl_i16__to_be_bytes (bytes: i16)
    : Prims.Pure (t_Array i16 (mk_usize 2)) Prims.l_True (fun _ -> Prims.l_True)

val impl_i16__to_le_bytes (bytes: i16)
    : Prims.Pure (t_Array i16 (mk_usize 2)) Prims.l_True (fun _ -> Prims.l_True)

val impl_i16__rem_euclid (x y: i16)
    : Prims.Pure i16 (requires y <>. mk_i16 0) (fun _ -> Prims.l_True)

val impl_i16__abs (x: i16) : Prims.Pure i16 (requires x >. impl_i16__MIN) (fun _ -> Prims.l_True)

let impl_i32__MIN: i32 = mk_i32 (-2147483648)

let impl_i32__MAX: i32 = mk_i32 2147483647

let impl_i32__BITS: u32 = mk_u32 32

val impl_i32__wrapping_add (x y: i32) : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i32__saturating_add (x y: i32) : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i32__overflowing_add (x y: i32)
    : Prims.Pure (i32 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_i32__wrapping_sub (x y: i32) : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i32__saturating_sub (x y: i32) : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i32__overflowing_sub (x y: i32)
    : Prims.Pure (i32 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_i32__wrapping_mul (x y: i32) : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i32__saturating_mul (x y: i32) : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i32__overflowing_mul (x y: i32)
    : Prims.Pure (i32 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_i32__pow (x: i32) (exp: u32) : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i32__count_ones (x: i32) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i32__rotate_right (x: i32) (n: u32) : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i32__rotate_left (x: i32) (n: u32) : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i32__leading_zeros (x: i32) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i32__ilog2 (x: i32) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i32__from_str_radix (src: string) (radix: u32)
    : Prims.Pure (Core_models.Result.t_Result i32 Core_models.Num.Error.t_ParseIntError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_i32__from_be_bytes (bytes: t_Array i32 (mk_usize 4))
    : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i32__from_le_bytes (bytes: t_Array i32 (mk_usize 4))
    : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i32__to_be_bytes (bytes: i32)
    : Prims.Pure (t_Array i32 (mk_usize 4)) Prims.l_True (fun _ -> Prims.l_True)

val impl_i32__to_le_bytes (bytes: i32)
    : Prims.Pure (t_Array i32 (mk_usize 4)) Prims.l_True (fun _ -> Prims.l_True)

val impl_i32__rem_euclid (x y: i32)
    : Prims.Pure i32 (requires y <>. mk_i32 0) (fun _ -> Prims.l_True)

val impl_i32__abs (x: i32) : Prims.Pure i32 (requires x >. impl_i32__MIN) (fun _ -> Prims.l_True)

let impl_i64__MIN: i64 = mk_i64 (-9223372036854775808)

let impl_i64__MAX: i64 = mk_i64 9223372036854775807

let impl_i64__BITS: u32 = mk_u32 64

val impl_i64__wrapping_add (x y: i64) : Prims.Pure i64 Prims.l_True (fun _ -> Prims.l_True)

val impl_i64__saturating_add (x y: i64) : Prims.Pure i64 Prims.l_True (fun _ -> Prims.l_True)

val impl_i64__overflowing_add (x y: i64)
    : Prims.Pure (i64 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_i64__wrapping_sub (x y: i64) : Prims.Pure i64 Prims.l_True (fun _ -> Prims.l_True)

val impl_i64__saturating_sub (x y: i64) : Prims.Pure i64 Prims.l_True (fun _ -> Prims.l_True)

val impl_i64__overflowing_sub (x y: i64)
    : Prims.Pure (i64 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_i64__wrapping_mul (x y: i64) : Prims.Pure i64 Prims.l_True (fun _ -> Prims.l_True)

val impl_i64__saturating_mul (x y: i64) : Prims.Pure i64 Prims.l_True (fun _ -> Prims.l_True)

val impl_i64__overflowing_mul (x y: i64)
    : Prims.Pure (i64 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_i64__pow (x: i64) (exp: u32) : Prims.Pure i64 Prims.l_True (fun _ -> Prims.l_True)

val impl_i64__count_ones (x: i64) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i64__rotate_right (x: i64) (n: u32) : Prims.Pure i64 Prims.l_True (fun _ -> Prims.l_True)

val impl_i64__rotate_left (x: i64) (n: u32) : Prims.Pure i64 Prims.l_True (fun _ -> Prims.l_True)

val impl_i64__leading_zeros (x: i64) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i64__ilog2 (x: i64) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i64__from_str_radix (src: string) (radix: u32)
    : Prims.Pure (Core_models.Result.t_Result i64 Core_models.Num.Error.t_ParseIntError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_i64__from_be_bytes (bytes: t_Array i64 (mk_usize 8))
    : Prims.Pure i64 Prims.l_True (fun _ -> Prims.l_True)

val impl_i64__from_le_bytes (bytes: t_Array i64 (mk_usize 8))
    : Prims.Pure i64 Prims.l_True (fun _ -> Prims.l_True)

val impl_i64__to_be_bytes (bytes: i64)
    : Prims.Pure (t_Array i64 (mk_usize 8)) Prims.l_True (fun _ -> Prims.l_True)

val impl_i64__to_le_bytes (bytes: i64)
    : Prims.Pure (t_Array i64 (mk_usize 8)) Prims.l_True (fun _ -> Prims.l_True)

val impl_i64__rem_euclid (x y: i64)
    : Prims.Pure i64 (requires y <>. mk_i64 0) (fun _ -> Prims.l_True)

val impl_i64__abs (x: i64) : Prims.Pure i64 (requires x >. impl_i64__MIN) (fun _ -> Prims.l_True)

let impl_i128__MIN: i128 = mk_i128 (-170141183460469231731687303715884105728)

let impl_i128__MAX: i128 = mk_i128 170141183460469231731687303715884105727

let impl_i128__BITS: u32 = mk_u32 128

val impl_i128__wrapping_add (x y: i128) : Prims.Pure i128 Prims.l_True (fun _ -> Prims.l_True)

val impl_i128__saturating_add (x y: i128) : Prims.Pure i128 Prims.l_True (fun _ -> Prims.l_True)

val impl_i128__overflowing_add (x y: i128)
    : Prims.Pure (i128 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_i128__wrapping_sub (x y: i128) : Prims.Pure i128 Prims.l_True (fun _ -> Prims.l_True)

val impl_i128__saturating_sub (x y: i128) : Prims.Pure i128 Prims.l_True (fun _ -> Prims.l_True)

val impl_i128__overflowing_sub (x y: i128)
    : Prims.Pure (i128 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_i128__wrapping_mul (x y: i128) : Prims.Pure i128 Prims.l_True (fun _ -> Prims.l_True)

val impl_i128__saturating_mul (x y: i128) : Prims.Pure i128 Prims.l_True (fun _ -> Prims.l_True)

val impl_i128__overflowing_mul (x y: i128)
    : Prims.Pure (i128 & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_i128__pow (x: i128) (exp: u32) : Prims.Pure i128 Prims.l_True (fun _ -> Prims.l_True)

val impl_i128__count_ones (x: i128) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i128__rotate_right (x: i128) (n: u32)
    : Prims.Pure i128 Prims.l_True (fun _ -> Prims.l_True)

val impl_i128__rotate_left (x: i128) (n: u32) : Prims.Pure i128 Prims.l_True (fun _ -> Prims.l_True)

val impl_i128__leading_zeros (x: i128) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i128__ilog2 (x: i128) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_i128__from_str_radix (src: string) (radix: u32)
    : Prims.Pure (Core_models.Result.t_Result i128 Core_models.Num.Error.t_ParseIntError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_i128__from_be_bytes (bytes: t_Array i128 (mk_usize 16))
    : Prims.Pure i128 Prims.l_True (fun _ -> Prims.l_True)

val impl_i128__from_le_bytes (bytes: t_Array i128 (mk_usize 16))
    : Prims.Pure i128 Prims.l_True (fun _ -> Prims.l_True)

val impl_i128__to_be_bytes (bytes: i128)
    : Prims.Pure (t_Array i128 (mk_usize 16)) Prims.l_True (fun _ -> Prims.l_True)

val impl_i128__to_le_bytes (bytes: i128)
    : Prims.Pure (t_Array i128 (mk_usize 16)) Prims.l_True (fun _ -> Prims.l_True)

val impl_i128__rem_euclid (x y: i128)
    : Prims.Pure i128 (requires y <>. mk_i128 0) (fun _ -> Prims.l_True)

val impl_i128__abs (x: i128)
    : Prims.Pure i128 (requires x >. impl_i128__MIN) (fun _ -> Prims.l_True)

let impl_isize__MIN: isize = Rust_primitives.Arithmetic.v_ISIZE_MIN

let impl_isize__MAX: isize = Rust_primitives.Arithmetic.v_ISIZE_MAX

let impl_isize__BITS: u32 = Rust_primitives.Arithmetic.v_SIZE_BITS

val impl_isize__wrapping_add (x y: isize) : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

val impl_isize__saturating_add (x y: isize) : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

val impl_isize__overflowing_add (x y: isize)
    : Prims.Pure (isize & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_isize__wrapping_sub (x y: isize) : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

val impl_isize__saturating_sub (x y: isize) : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

val impl_isize__overflowing_sub (x y: isize)
    : Prims.Pure (isize & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_isize__wrapping_mul (x y: isize) : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

val impl_isize__saturating_mul (x y: isize) : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

val impl_isize__overflowing_mul (x y: isize)
    : Prims.Pure (isize & bool) Prims.l_True (fun _ -> Prims.l_True)

val impl_isize__pow (x: isize) (exp: u32) : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

val impl_isize__count_ones (x: isize) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_isize__rotate_right (x: isize) (n: u32)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

val impl_isize__rotate_left (x: isize) (n: u32)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

val impl_isize__leading_zeros (x: isize) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_isize__ilog2 (x: isize) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_isize__from_str_radix (src: string) (radix: u32)
    : Prims.Pure (Core_models.Result.t_Result isize Core_models.Num.Error.t_ParseIntError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_isize__from_be_bytes (bytes: t_Array isize (mk_usize 0))
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

val impl_isize__from_le_bytes (bytes: t_Array isize (mk_usize 0))
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

val impl_isize__to_be_bytes (bytes: isize)
    : Prims.Pure (t_Array isize (mk_usize 0)) Prims.l_True (fun _ -> Prims.l_True)

val impl_isize__to_le_bytes (bytes: isize)
    : Prims.Pure (t_Array isize (mk_usize 0)) Prims.l_True (fun _ -> Prims.l_True)

val impl_isize__rem_euclid (x y: isize)
    : Prims.Pure isize (requires y <>. mk_isize 0) (fun _ -> Prims.l_True)

val impl_isize__abs (x: isize)
    : Prims.Pure isize (requires x >. impl_isize__MIN) (fun _ -> Prims.l_True)

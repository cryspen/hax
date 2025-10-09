module Core_models.Num
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul

open Rust_primitives.Integers

open Rust_primitives.Arrays

let impl_u8__MIN: u8 = mk_u8 0

let impl_u8__MAX: u8 = mk_u8 255

let impl_u8__BITS: u32 = mk_u32 8

let impl_u8__wrapping_add (x y: u8) : u8 = Rust_primitives.Arithmetic.wrapping_add_u8 x y

let impl_u8__saturating_add (x y: u8) : u8 = Rust_primitives.Arithmetic.saturating_add_u8 x y

let impl_u8__overflowing_add (x y: u8) : (u8 & bool) =
  Rust_primitives.Arithmetic.overflowing_add_u8 x y

let impl_u8__wrapping_sub (x y: u8) : u8 = Rust_primitives.Arithmetic.wrapping_sub_u8 x y

let impl_u8__saturating_sub (x y: u8) : u8 = Rust_primitives.Arithmetic.saturating_sub_u8 x y

let impl_u8__overflowing_sub (x y: u8) : (u8 & bool) =
  Rust_primitives.Arithmetic.overflowing_sub_u8 x y

let impl_u8__wrapping_mul (x y: u8) : u8 = Rust_primitives.Arithmetic.wrapping_mul_u8 x y

let impl_u8__saturating_mul (x y: u8) : u8 = Rust_primitives.Arithmetic.saturating_mul_u8 x y

let impl_u8__overflowing_mul (x y: u8) : (u8 & bool) =
  Rust_primitives.Arithmetic.overflowing_mul_u8 x y

let impl_u8__pow (x: u8) (exp: u32) : u8 = Rust_primitives.Arithmetic.pow_u8 x exp

let impl_u8__count_ones (x: u8) : u32 = Rust_primitives.Arithmetic.count_ones_u8 x

assume
val impl_u8__rotate_right': x: u8 -> n: u32 -> u8

unfold
let impl_u8__rotate_right = impl_u8__rotate_right'

assume
val impl_u8__rotate_left': x: u8 -> n: u32 -> u8

unfold
let impl_u8__rotate_left = impl_u8__rotate_left'

assume
val impl_u8__leading_zeros': x: u8 -> u32

unfold
let impl_u8__leading_zeros = impl_u8__leading_zeros'

assume
val impl_u8__ilog2': x: u8 -> u32

unfold
let impl_u8__ilog2 = impl_u8__ilog2'

assume
val impl_u8__from_str_radix': src: string -> radix: u32
  -> Core_models.Result.t_Result u8 Core_models.Num.Error.t_ParseIntError

unfold
let impl_u8__from_str_radix = impl_u8__from_str_radix'

assume
val impl_u8__from_be_bytes': bytes: t_Array u8 (mk_usize 1) -> u8

unfold
let impl_u8__from_be_bytes = impl_u8__from_be_bytes'

assume
val impl_u8__from_le_bytes': bytes: t_Array u8 (mk_usize 1) -> u8

unfold
let impl_u8__from_le_bytes = impl_u8__from_le_bytes'

assume
val impl_u8__to_be_bytes': bytes: u8 -> t_Array u8 (mk_usize 1)

unfold
let impl_u8__to_be_bytes = impl_u8__to_be_bytes'

assume
val impl_u8__to_le_bytes': bytes: u8 -> t_Array u8 (mk_usize 1)

unfold
let impl_u8__to_le_bytes = impl_u8__to_le_bytes'

let impl_u8__rem_euclid (x y: u8) : Prims.Pure u8 (requires y <>. mk_u8 0) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.rem_euclid_u8 x y

let impl_u16__MIN: u16 = mk_u16 0

let impl_u16__MAX: u16 = mk_u16 65535

let impl_u16__BITS: u32 = mk_u32 16

let impl_u16__wrapping_add (x y: u16) : u16 = Rust_primitives.Arithmetic.wrapping_add_u16 x y

let impl_u16__saturating_add (x y: u16) : u16 = Rust_primitives.Arithmetic.saturating_add_u16 x y

let impl_u16__overflowing_add (x y: u16) : (u16 & bool) =
  Rust_primitives.Arithmetic.overflowing_add_u16 x y

let impl_u16__wrapping_sub (x y: u16) : u16 = Rust_primitives.Arithmetic.wrapping_sub_u16 x y

let impl_u16__saturating_sub (x y: u16) : u16 = Rust_primitives.Arithmetic.saturating_sub_u16 x y

let impl_u16__overflowing_sub (x y: u16) : (u16 & bool) =
  Rust_primitives.Arithmetic.overflowing_sub_u16 x y

let impl_u16__wrapping_mul (x y: u16) : u16 = Rust_primitives.Arithmetic.wrapping_mul_u16 x y

let impl_u16__saturating_mul (x y: u16) : u16 = Rust_primitives.Arithmetic.saturating_mul_u16 x y

let impl_u16__overflowing_mul (x y: u16) : (u16 & bool) =
  Rust_primitives.Arithmetic.overflowing_mul_u16 x y

let impl_u16__pow (x: u16) (exp: u32) : u16 = Rust_primitives.Arithmetic.pow_u16 x exp

let impl_u16__count_ones (x: u16) : u32 = Rust_primitives.Arithmetic.count_ones_u16 x

assume
val impl_u16__rotate_right': x: u16 -> n: u32 -> u16

unfold
let impl_u16__rotate_right = impl_u16__rotate_right'

assume
val impl_u16__rotate_left': x: u16 -> n: u32 -> u16

unfold
let impl_u16__rotate_left = impl_u16__rotate_left'

assume
val impl_u16__leading_zeros': x: u16 -> u32

unfold
let impl_u16__leading_zeros = impl_u16__leading_zeros'

assume
val impl_u16__ilog2': x: u16 -> u32

unfold
let impl_u16__ilog2 = impl_u16__ilog2'

assume
val impl_u16__from_str_radix': src: string -> radix: u32
  -> Core_models.Result.t_Result u16 Core_models.Num.Error.t_ParseIntError

unfold
let impl_u16__from_str_radix = impl_u16__from_str_radix'

assume
val impl_u16__from_be_bytes': bytes: t_Array u16 (mk_usize 2) -> u16

unfold
let impl_u16__from_be_bytes = impl_u16__from_be_bytes'

assume
val impl_u16__from_le_bytes': bytes: t_Array u16 (mk_usize 2) -> u16

unfold
let impl_u16__from_le_bytes = impl_u16__from_le_bytes'

assume
val impl_u16__to_be_bytes': bytes: u16 -> t_Array u16 (mk_usize 2)

unfold
let impl_u16__to_be_bytes = impl_u16__to_be_bytes'

assume
val impl_u16__to_le_bytes': bytes: u16 -> t_Array u16 (mk_usize 2)

unfold
let impl_u16__to_le_bytes = impl_u16__to_le_bytes'

let impl_u16__rem_euclid (x y: u16)
    : Prims.Pure u16 (requires y <>. mk_u16 0) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.rem_euclid_u16 x y

let impl_u32__MIN: u32 = mk_u32 0

let impl_u32__MAX: u32 = mk_u32 4294967295

let impl_u32__BITS: u32 = mk_u32 32

let impl_u32__wrapping_add (x y: u32) : u32 = Rust_primitives.Arithmetic.wrapping_add_u32 x y

let impl_u32__saturating_add (x y: u32) : u32 = Rust_primitives.Arithmetic.saturating_add_u32 x y

let impl_u32__overflowing_add (x y: u32) : (u32 & bool) =
  Rust_primitives.Arithmetic.overflowing_add_u32 x y

let impl_u32__wrapping_sub (x y: u32) : u32 = Rust_primitives.Arithmetic.wrapping_sub_u32 x y

let impl_u32__saturating_sub (x y: u32) : u32 = Rust_primitives.Arithmetic.saturating_sub_u32 x y

let impl_u32__overflowing_sub (x y: u32) : (u32 & bool) =
  Rust_primitives.Arithmetic.overflowing_sub_u32 x y

let impl_u32__wrapping_mul (x y: u32) : u32 = Rust_primitives.Arithmetic.wrapping_mul_u32 x y

let impl_u32__saturating_mul (x y: u32) : u32 = Rust_primitives.Arithmetic.saturating_mul_u32 x y

let impl_u32__overflowing_mul (x y: u32) : (u32 & bool) =
  Rust_primitives.Arithmetic.overflowing_mul_u32 x y

let impl_u32__pow (x exp: u32) : u32 = Rust_primitives.Arithmetic.pow_u32 x exp

let impl_u32__count_ones (x: u32) : u32 = Rust_primitives.Arithmetic.count_ones_u32 x

assume
val impl_u32__rotate_right': x: u32 -> n: u32 -> u32

unfold
let impl_u32__rotate_right = impl_u32__rotate_right'

assume
val impl_u32__rotate_left': x: u32 -> n: u32 -> u32

unfold
let impl_u32__rotate_left = impl_u32__rotate_left'

assume
val impl_u32__leading_zeros': x: u32 -> u32

unfold
let impl_u32__leading_zeros = impl_u32__leading_zeros'

assume
val impl_u32__ilog2': x: u32 -> u32

unfold
let impl_u32__ilog2 = impl_u32__ilog2'

assume
val impl_u32__from_str_radix': src: string -> radix: u32
  -> Core_models.Result.t_Result u32 Core_models.Num.Error.t_ParseIntError

unfold
let impl_u32__from_str_radix = impl_u32__from_str_radix'

assume
val impl_u32__from_be_bytes': bytes: t_Array u32 (mk_usize 4) -> u32

unfold
let impl_u32__from_be_bytes = impl_u32__from_be_bytes'

assume
val impl_u32__from_le_bytes': bytes: t_Array u32 (mk_usize 4) -> u32

unfold
let impl_u32__from_le_bytes = impl_u32__from_le_bytes'

assume
val impl_u32__to_be_bytes': bytes: u32 -> t_Array u32 (mk_usize 4)

unfold
let impl_u32__to_be_bytes = impl_u32__to_be_bytes'

assume
val impl_u32__to_le_bytes': bytes: u32 -> t_Array u32 (mk_usize 4)

unfold
let impl_u32__to_le_bytes = impl_u32__to_le_bytes'

let impl_u32__rem_euclid (x y: u32)
    : Prims.Pure u32 (requires y <>. mk_u32 0) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.rem_euclid_u32 x y

let impl_u64__MIN: u64 = mk_u64 0

let impl_u64__MAX: u64 = mk_u64 18446744073709551615

let impl_u64__BITS: u32 = mk_u32 64

let impl_u64__wrapping_add (x y: u64) : u64 = Rust_primitives.Arithmetic.wrapping_add_u64 x y

let impl_u64__saturating_add (x y: u64) : u64 = Rust_primitives.Arithmetic.saturating_add_u64 x y

let impl_u64__overflowing_add (x y: u64) : (u64 & bool) =
  Rust_primitives.Arithmetic.overflowing_add_u64 x y

let impl_u64__wrapping_sub (x y: u64) : u64 = Rust_primitives.Arithmetic.wrapping_sub_u64 x y

let impl_u64__saturating_sub (x y: u64) : u64 = Rust_primitives.Arithmetic.saturating_sub_u64 x y

let impl_u64__overflowing_sub (x y: u64) : (u64 & bool) =
  Rust_primitives.Arithmetic.overflowing_sub_u64 x y

let impl_u64__wrapping_mul (x y: u64) : u64 = Rust_primitives.Arithmetic.wrapping_mul_u64 x y

let impl_u64__saturating_mul (x y: u64) : u64 = Rust_primitives.Arithmetic.saturating_mul_u64 x y

let impl_u64__overflowing_mul (x y: u64) : (u64 & bool) =
  Rust_primitives.Arithmetic.overflowing_mul_u64 x y

let impl_u64__pow (x: u64) (exp: u32) : u64 = Rust_primitives.Arithmetic.pow_u64 x exp

let impl_u64__count_ones (x: u64) : u32 = Rust_primitives.Arithmetic.count_ones_u64 x

assume
val impl_u64__rotate_right': x: u64 -> n: u32 -> u64

unfold
let impl_u64__rotate_right = impl_u64__rotate_right'

assume
val impl_u64__rotate_left': x: u64 -> n: u32 -> u64

unfold
let impl_u64__rotate_left = impl_u64__rotate_left'

assume
val impl_u64__leading_zeros': x: u64 -> u32

unfold
let impl_u64__leading_zeros = impl_u64__leading_zeros'

assume
val impl_u64__ilog2': x: u64 -> u32

unfold
let impl_u64__ilog2 = impl_u64__ilog2'

assume
val impl_u64__from_str_radix': src: string -> radix: u32
  -> Core_models.Result.t_Result u64 Core_models.Num.Error.t_ParseIntError

unfold
let impl_u64__from_str_radix = impl_u64__from_str_radix'

assume
val impl_u64__from_be_bytes': bytes: t_Array u64 (mk_usize 8) -> u64

unfold
let impl_u64__from_be_bytes = impl_u64__from_be_bytes'

assume
val impl_u64__from_le_bytes': bytes: t_Array u64 (mk_usize 8) -> u64

unfold
let impl_u64__from_le_bytes = impl_u64__from_le_bytes'

assume
val impl_u64__to_be_bytes': bytes: u64 -> t_Array u64 (mk_usize 8)

unfold
let impl_u64__to_be_bytes = impl_u64__to_be_bytes'

assume
val impl_u64__to_le_bytes': bytes: u64 -> t_Array u64 (mk_usize 8)

unfold
let impl_u64__to_le_bytes = impl_u64__to_le_bytes'

let impl_u64__rem_euclid (x y: u64)
    : Prims.Pure u64 (requires y <>. mk_u64 0) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.rem_euclid_u64 x y

let impl_u128__MIN: u128 = mk_u128 0

let impl_u128__MAX: u128 = mk_u128 340282366920938463463374607431768211455

let impl_u128__BITS: u32 = mk_u32 128

let impl_u128__wrapping_add (x y: u128) : u128 = Rust_primitives.Arithmetic.wrapping_add_u128 x y

let impl_u128__saturating_add (x y: u128) : u128 =
  Rust_primitives.Arithmetic.saturating_add_u128 x y

let impl_u128__overflowing_add (x y: u128) : (u128 & bool) =
  Rust_primitives.Arithmetic.overflowing_add_u128 x y

let impl_u128__wrapping_sub (x y: u128) : u128 = Rust_primitives.Arithmetic.wrapping_sub_u128 x y

let impl_u128__saturating_sub (x y: u128) : u128 =
  Rust_primitives.Arithmetic.saturating_sub_u128 x y

let impl_u128__overflowing_sub (x y: u128) : (u128 & bool) =
  Rust_primitives.Arithmetic.overflowing_sub_u128 x y

let impl_u128__wrapping_mul (x y: u128) : u128 = Rust_primitives.Arithmetic.wrapping_mul_u128 x y

let impl_u128__saturating_mul (x y: u128) : u128 =
  Rust_primitives.Arithmetic.saturating_mul_u128 x y

let impl_u128__overflowing_mul (x y: u128) : (u128 & bool) =
  Rust_primitives.Arithmetic.overflowing_mul_u128 x y

let impl_u128__pow (x: u128) (exp: u32) : u128 = Rust_primitives.Arithmetic.pow_u128 x exp

let impl_u128__count_ones (x: u128) : u32 = Rust_primitives.Arithmetic.count_ones_u128 x

assume
val impl_u128__rotate_right': x: u128 -> n: u32 -> u128

unfold
let impl_u128__rotate_right = impl_u128__rotate_right'

assume
val impl_u128__rotate_left': x: u128 -> n: u32 -> u128

unfold
let impl_u128__rotate_left = impl_u128__rotate_left'

assume
val impl_u128__leading_zeros': x: u128 -> u32

unfold
let impl_u128__leading_zeros = impl_u128__leading_zeros'

assume
val impl_u128__ilog2': x: u128 -> u32

unfold
let impl_u128__ilog2 = impl_u128__ilog2'

assume
val impl_u128__from_str_radix': src: string -> radix: u32
  -> Core_models.Result.t_Result u128 Core_models.Num.Error.t_ParseIntError

unfold
let impl_u128__from_str_radix = impl_u128__from_str_radix'

assume
val impl_u128__from_be_bytes': bytes: t_Array u128 (mk_usize 16) -> u128

unfold
let impl_u128__from_be_bytes = impl_u128__from_be_bytes'

assume
val impl_u128__from_le_bytes': bytes: t_Array u128 (mk_usize 16) -> u128

unfold
let impl_u128__from_le_bytes = impl_u128__from_le_bytes'

assume
val impl_u128__to_be_bytes': bytes: u128 -> t_Array u128 (mk_usize 16)

unfold
let impl_u128__to_be_bytes = impl_u128__to_be_bytes'

assume
val impl_u128__to_le_bytes': bytes: u128 -> t_Array u128 (mk_usize 16)

unfold
let impl_u128__to_le_bytes = impl_u128__to_le_bytes'

let impl_u128__rem_euclid (x y: u128)
    : Prims.Pure u128 (requires y <>. mk_u128 0) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.rem_euclid_u128 x y

let impl_usize__MIN: usize = mk_usize 0

let impl_usize__MAX: usize = Rust_primitives.Arithmetic.v_USIZE_MAX

let impl_usize__BITS: u32 = Rust_primitives.Arithmetic.v_SIZE_BITS

let impl_usize__wrapping_add (x y: usize) : usize =
  Rust_primitives.Arithmetic.wrapping_add_usize x y

let impl_usize__saturating_add (x y: usize) : usize =
  Rust_primitives.Arithmetic.saturating_add_usize x y

let impl_usize__overflowing_add (x y: usize) : (usize & bool) =
  Rust_primitives.Arithmetic.overflowing_add_usize x y

let impl_usize__wrapping_sub (x y: usize) : usize =
  Rust_primitives.Arithmetic.wrapping_sub_usize x y

let impl_usize__saturating_sub (x y: usize) : usize =
  Rust_primitives.Arithmetic.saturating_sub_usize x y

let impl_usize__overflowing_sub (x y: usize) : (usize & bool) =
  Rust_primitives.Arithmetic.overflowing_sub_usize x y

let impl_usize__wrapping_mul (x y: usize) : usize =
  Rust_primitives.Arithmetic.wrapping_mul_usize x y

let impl_usize__saturating_mul (x y: usize) : usize =
  Rust_primitives.Arithmetic.saturating_mul_usize x y

let impl_usize__overflowing_mul (x y: usize) : (usize & bool) =
  Rust_primitives.Arithmetic.overflowing_mul_usize x y

let impl_usize__pow (x: usize) (exp: u32) : usize = Rust_primitives.Arithmetic.pow_usize x exp

let impl_usize__count_ones (x: usize) : u32 = Rust_primitives.Arithmetic.count_ones_usize x

assume
val impl_usize__rotate_right': x: usize -> n: u32 -> usize

unfold
let impl_usize__rotate_right = impl_usize__rotate_right'

assume
val impl_usize__rotate_left': x: usize -> n: u32 -> usize

unfold
let impl_usize__rotate_left = impl_usize__rotate_left'

assume
val impl_usize__leading_zeros': x: usize -> u32

unfold
let impl_usize__leading_zeros = impl_usize__leading_zeros'

assume
val impl_usize__ilog2': x: usize -> u32

unfold
let impl_usize__ilog2 = impl_usize__ilog2'

assume
val impl_usize__from_str_radix': src: string -> radix: u32
  -> Core_models.Result.t_Result usize Core_models.Num.Error.t_ParseIntError

unfold
let impl_usize__from_str_radix = impl_usize__from_str_radix'

assume
val impl_usize__from_be_bytes': bytes: t_Array usize (mk_usize 0) -> usize

unfold
let impl_usize__from_be_bytes = impl_usize__from_be_bytes'

assume
val impl_usize__from_le_bytes': bytes: t_Array usize (mk_usize 0) -> usize

unfold
let impl_usize__from_le_bytes = impl_usize__from_le_bytes'

assume
val impl_usize__to_be_bytes': bytes: usize -> t_Array usize (mk_usize 0)

unfold
let impl_usize__to_be_bytes = impl_usize__to_be_bytes'

assume
val impl_usize__to_le_bytes': bytes: usize -> t_Array usize (mk_usize 0)

unfold
let impl_usize__to_le_bytes = impl_usize__to_le_bytes'

let impl_usize__rem_euclid (x y: usize)
    : Prims.Pure usize (requires y <>. mk_usize 0) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.rem_euclid_usize x y

let impl_i8__MIN: i8 = mk_i8 (-128)

let impl_i8__MAX: i8 = mk_i8 127

let impl_i8__BITS: u32 = mk_u32 8

let impl_i8__wrapping_add (x y: i8) : i8 = Rust_primitives.Arithmetic.wrapping_add_i8 x y

let impl_i8__saturating_add (x y: i8) : i8 = Rust_primitives.Arithmetic.saturating_add_i8 x y

let impl_i8__overflowing_add (x y: i8) : (i8 & bool) =
  Rust_primitives.Arithmetic.overflowing_add_i8 x y

let impl_i8__wrapping_sub (x y: i8) : i8 = Rust_primitives.Arithmetic.wrapping_sub_i8 x y

let impl_i8__saturating_sub (x y: i8) : i8 = Rust_primitives.Arithmetic.saturating_sub_i8 x y

let impl_i8__overflowing_sub (x y: i8) : (i8 & bool) =
  Rust_primitives.Arithmetic.overflowing_sub_i8 x y

let impl_i8__wrapping_mul (x y: i8) : i8 = Rust_primitives.Arithmetic.wrapping_mul_i8 x y

let impl_i8__saturating_mul (x y: i8) : i8 = Rust_primitives.Arithmetic.saturating_mul_i8 x y

let impl_i8__overflowing_mul (x y: i8) : (i8 & bool) =
  Rust_primitives.Arithmetic.overflowing_mul_i8 x y

let impl_i8__pow (x: i8) (exp: u32) : i8 = Rust_primitives.Arithmetic.pow_i8 x exp

let impl_i8__count_ones (x: i8) : u32 = Rust_primitives.Arithmetic.count_ones_i8 x

assume
val impl_i8__rotate_right': x: i8 -> n: u32 -> i8

unfold
let impl_i8__rotate_right = impl_i8__rotate_right'

assume
val impl_i8__rotate_left': x: i8 -> n: u32 -> i8

unfold
let impl_i8__rotate_left = impl_i8__rotate_left'

assume
val impl_i8__leading_zeros': x: i8 -> u32

unfold
let impl_i8__leading_zeros = impl_i8__leading_zeros'

assume
val impl_i8__ilog2': x: i8 -> u32

unfold
let impl_i8__ilog2 = impl_i8__ilog2'

assume
val impl_i8__from_str_radix': src: string -> radix: u32
  -> Core_models.Result.t_Result i8 Core_models.Num.Error.t_ParseIntError

unfold
let impl_i8__from_str_radix = impl_i8__from_str_radix'

assume
val impl_i8__from_be_bytes': bytes: t_Array i8 (mk_usize 1) -> i8

unfold
let impl_i8__from_be_bytes = impl_i8__from_be_bytes'

assume
val impl_i8__from_le_bytes': bytes: t_Array i8 (mk_usize 1) -> i8

unfold
let impl_i8__from_le_bytes = impl_i8__from_le_bytes'

assume
val impl_i8__to_be_bytes': bytes: i8 -> t_Array i8 (mk_usize 1)

unfold
let impl_i8__to_be_bytes = impl_i8__to_be_bytes'

assume
val impl_i8__to_le_bytes': bytes: i8 -> t_Array i8 (mk_usize 1)

unfold
let impl_i8__to_le_bytes = impl_i8__to_le_bytes'

let impl_i8__rem_euclid (x y: i8) : Prims.Pure i8 (requires y <>. mk_i8 0) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.rem_euclid_i8 x y

let impl_i8__abs (x: i8) : Prims.Pure bool (requires x >. impl_i8__MIN) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.abs_i8 x

let impl_i16__MIN: i16 = mk_i16 (-32768)

let impl_i16__MAX: i16 = mk_i16 32767

let impl_i16__BITS: u32 = mk_u32 16

let impl_i16__wrapping_add (x y: i16) : i16 = Rust_primitives.Arithmetic.wrapping_add_i16 x y

let impl_i16__saturating_add (x y: i16) : i16 = Rust_primitives.Arithmetic.saturating_add_i16 x y

let impl_i16__overflowing_add (x y: i16) : (i16 & bool) =
  Rust_primitives.Arithmetic.overflowing_add_i16 x y

let impl_i16__wrapping_sub (x y: i16) : i16 = Rust_primitives.Arithmetic.wrapping_sub_i16 x y

let impl_i16__saturating_sub (x y: i16) : i16 = Rust_primitives.Arithmetic.saturating_sub_i16 x y

let impl_i16__overflowing_sub (x y: i16) : (i16 & bool) =
  Rust_primitives.Arithmetic.overflowing_sub_i16 x y

let impl_i16__wrapping_mul (x y: i16) : i16 = Rust_primitives.Arithmetic.wrapping_mul_i16 x y

let impl_i16__saturating_mul (x y: i16) : i16 = Rust_primitives.Arithmetic.saturating_mul_i16 x y

let impl_i16__overflowing_mul (x y: i16) : (i16 & bool) =
  Rust_primitives.Arithmetic.overflowing_mul_i16 x y

let impl_i16__pow (x: i16) (exp: u32) : i16 = Rust_primitives.Arithmetic.pow_i16 x exp

let impl_i16__count_ones (x: i16) : u32 = Rust_primitives.Arithmetic.count_ones_i16 x

assume
val impl_i16__rotate_right': x: i16 -> n: u32 -> i16

unfold
let impl_i16__rotate_right = impl_i16__rotate_right'

assume
val impl_i16__rotate_left': x: i16 -> n: u32 -> i16

unfold
let impl_i16__rotate_left = impl_i16__rotate_left'

assume
val impl_i16__leading_zeros': x: i16 -> u32

unfold
let impl_i16__leading_zeros = impl_i16__leading_zeros'

assume
val impl_i16__ilog2': x: i16 -> u32

unfold
let impl_i16__ilog2 = impl_i16__ilog2'

assume
val impl_i16__from_str_radix': src: string -> radix: u32
  -> Core_models.Result.t_Result i16 Core_models.Num.Error.t_ParseIntError

unfold
let impl_i16__from_str_radix = impl_i16__from_str_radix'

assume
val impl_i16__from_be_bytes': bytes: t_Array i16 (mk_usize 2) -> i16

unfold
let impl_i16__from_be_bytes = impl_i16__from_be_bytes'

assume
val impl_i16__from_le_bytes': bytes: t_Array i16 (mk_usize 2) -> i16

unfold
let impl_i16__from_le_bytes = impl_i16__from_le_bytes'

assume
val impl_i16__to_be_bytes': bytes: i16 -> t_Array i16 (mk_usize 2)

unfold
let impl_i16__to_be_bytes = impl_i16__to_be_bytes'

assume
val impl_i16__to_le_bytes': bytes: i16 -> t_Array i16 (mk_usize 2)

unfold
let impl_i16__to_le_bytes = impl_i16__to_le_bytes'

let impl_i16__rem_euclid (x y: i16)
    : Prims.Pure i16 (requires y <>. mk_i16 0) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.rem_euclid_i16 x y

let impl_i16__abs (x: i16) : Prims.Pure bool (requires x >. impl_i16__MIN) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.abs_i16 x

let impl_i32__MIN: i32 = mk_i32 (-2147483648)

let impl_i32__MAX: i32 = mk_i32 2147483647

let impl_i32__BITS: u32 = mk_u32 32

let impl_i32__wrapping_add (x y: i32) : i32 = Rust_primitives.Arithmetic.wrapping_add_i32 x y

let impl_i32__saturating_add (x y: i32) : i32 = Rust_primitives.Arithmetic.saturating_add_i32 x y

let impl_i32__overflowing_add (x y: i32) : (i32 & bool) =
  Rust_primitives.Arithmetic.overflowing_add_i32 x y

let impl_i32__wrapping_sub (x y: i32) : i32 = Rust_primitives.Arithmetic.wrapping_sub_i32 x y

let impl_i32__saturating_sub (x y: i32) : i32 = Rust_primitives.Arithmetic.saturating_sub_i32 x y

let impl_i32__overflowing_sub (x y: i32) : (i32 & bool) =
  Rust_primitives.Arithmetic.overflowing_sub_i32 x y

let impl_i32__wrapping_mul (x y: i32) : i32 = Rust_primitives.Arithmetic.wrapping_mul_i32 x y

let impl_i32__saturating_mul (x y: i32) : i32 = Rust_primitives.Arithmetic.saturating_mul_i32 x y

let impl_i32__overflowing_mul (x y: i32) : (i32 & bool) =
  Rust_primitives.Arithmetic.overflowing_mul_i32 x y

let impl_i32__pow (x: i32) (exp: u32) : i32 = Rust_primitives.Arithmetic.pow_i32 x exp

let impl_i32__count_ones (x: i32) : u32 = Rust_primitives.Arithmetic.count_ones_i32 x

assume
val impl_i32__rotate_right': x: i32 -> n: u32 -> i32

unfold
let impl_i32__rotate_right = impl_i32__rotate_right'

assume
val impl_i32__rotate_left': x: i32 -> n: u32 -> i32

unfold
let impl_i32__rotate_left = impl_i32__rotate_left'

assume
val impl_i32__leading_zeros': x: i32 -> u32

unfold
let impl_i32__leading_zeros = impl_i32__leading_zeros'

assume
val impl_i32__ilog2': x: i32 -> u32

unfold
let impl_i32__ilog2 = impl_i32__ilog2'

assume
val impl_i32__from_str_radix': src: string -> radix: u32
  -> Core_models.Result.t_Result i32 Core_models.Num.Error.t_ParseIntError

unfold
let impl_i32__from_str_radix = impl_i32__from_str_radix'

assume
val impl_i32__from_be_bytes': bytes: t_Array i32 (mk_usize 4) -> i32

unfold
let impl_i32__from_be_bytes = impl_i32__from_be_bytes'

assume
val impl_i32__from_le_bytes': bytes: t_Array i32 (mk_usize 4) -> i32

unfold
let impl_i32__from_le_bytes = impl_i32__from_le_bytes'

assume
val impl_i32__to_be_bytes': bytes: i32 -> t_Array i32 (mk_usize 4)

unfold
let impl_i32__to_be_bytes = impl_i32__to_be_bytes'

assume
val impl_i32__to_le_bytes': bytes: i32 -> t_Array i32 (mk_usize 4)

unfold
let impl_i32__to_le_bytes = impl_i32__to_le_bytes'

let impl_i32__rem_euclid (x y: i32)
    : Prims.Pure i32 (requires y <>. mk_i32 0) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.rem_euclid_i32 x y

let impl_i32__abs (x: i32) : Prims.Pure bool (requires x >. impl_i32__MIN) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.abs_i32 x

let impl_i64__MIN: i64 = mk_i64 (-9223372036854775808)

let impl_i64__MAX: i64 = mk_i64 9223372036854775807

let impl_i64__BITS: u32 = mk_u32 64

let impl_i64__wrapping_add (x y: i64) : i64 = Rust_primitives.Arithmetic.wrapping_add_i64 x y

let impl_i64__saturating_add (x y: i64) : i64 = Rust_primitives.Arithmetic.saturating_add_i64 x y

let impl_i64__overflowing_add (x y: i64) : (i64 & bool) =
  Rust_primitives.Arithmetic.overflowing_add_i64 x y

let impl_i64__wrapping_sub (x y: i64) : i64 = Rust_primitives.Arithmetic.wrapping_sub_i64 x y

let impl_i64__saturating_sub (x y: i64) : i64 = Rust_primitives.Arithmetic.saturating_sub_i64 x y

let impl_i64__overflowing_sub (x y: i64) : (i64 & bool) =
  Rust_primitives.Arithmetic.overflowing_sub_i64 x y

let impl_i64__wrapping_mul (x y: i64) : i64 = Rust_primitives.Arithmetic.wrapping_mul_i64 x y

let impl_i64__saturating_mul (x y: i64) : i64 = Rust_primitives.Arithmetic.saturating_mul_i64 x y

let impl_i64__overflowing_mul (x y: i64) : (i64 & bool) =
  Rust_primitives.Arithmetic.overflowing_mul_i64 x y

let impl_i64__pow (x: i64) (exp: u32) : i64 = Rust_primitives.Arithmetic.pow_i64 x exp

let impl_i64__count_ones (x: i64) : u32 = Rust_primitives.Arithmetic.count_ones_i64 x

assume
val impl_i64__rotate_right': x: i64 -> n: u32 -> i64

unfold
let impl_i64__rotate_right = impl_i64__rotate_right'

assume
val impl_i64__rotate_left': x: i64 -> n: u32 -> i64

unfold
let impl_i64__rotate_left = impl_i64__rotate_left'

assume
val impl_i64__leading_zeros': x: i64 -> u32

unfold
let impl_i64__leading_zeros = impl_i64__leading_zeros'

assume
val impl_i64__ilog2': x: i64 -> u32

unfold
let impl_i64__ilog2 = impl_i64__ilog2'

assume
val impl_i64__from_str_radix': src: string -> radix: u32
  -> Core_models.Result.t_Result i64 Core_models.Num.Error.t_ParseIntError

unfold
let impl_i64__from_str_radix = impl_i64__from_str_radix'

assume
val impl_i64__from_be_bytes': bytes: t_Array i64 (mk_usize 8) -> i64

unfold
let impl_i64__from_be_bytes = impl_i64__from_be_bytes'

assume
val impl_i64__from_le_bytes': bytes: t_Array i64 (mk_usize 8) -> i64

unfold
let impl_i64__from_le_bytes = impl_i64__from_le_bytes'

assume
val impl_i64__to_be_bytes': bytes: i64 -> t_Array i64 (mk_usize 8)

unfold
let impl_i64__to_be_bytes = impl_i64__to_be_bytes'

assume
val impl_i64__to_le_bytes': bytes: i64 -> t_Array i64 (mk_usize 8)

unfold
let impl_i64__to_le_bytes = impl_i64__to_le_bytes'

let impl_i64__rem_euclid (x y: i64)
    : Prims.Pure i64 (requires y <>. mk_i64 0) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.rem_euclid_i64 x y

let impl_i64__abs (x: i64) : Prims.Pure bool (requires x >. impl_i64__MIN) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.abs_i64 x

let impl_i128__MIN: i128 = mk_i128 (-170141183460469231731687303715884105728)

let impl_i128__MAX: i128 = mk_i128 170141183460469231731687303715884105727

let impl_i128__BITS: u32 = mk_u32 128

let impl_i128__wrapping_add (x y: i128) : i128 = Rust_primitives.Arithmetic.wrapping_add_i128 x y

let impl_i128__saturating_add (x y: i128) : i128 =
  Rust_primitives.Arithmetic.saturating_add_i128 x y

let impl_i128__overflowing_add (x y: i128) : (i128 & bool) =
  Rust_primitives.Arithmetic.overflowing_add_i128 x y

let impl_i128__wrapping_sub (x y: i128) : i128 = Rust_primitives.Arithmetic.wrapping_sub_i128 x y

let impl_i128__saturating_sub (x y: i128) : i128 =
  Rust_primitives.Arithmetic.saturating_sub_i128 x y

let impl_i128__overflowing_sub (x y: i128) : (i128 & bool) =
  Rust_primitives.Arithmetic.overflowing_sub_i128 x y

let impl_i128__wrapping_mul (x y: i128) : i128 = Rust_primitives.Arithmetic.wrapping_mul_i128 x y

let impl_i128__saturating_mul (x y: i128) : i128 =
  Rust_primitives.Arithmetic.saturating_mul_i128 x y

let impl_i128__overflowing_mul (x y: i128) : (i128 & bool) =
  Rust_primitives.Arithmetic.overflowing_mul_i128 x y

let impl_i128__pow (x: i128) (exp: u32) : i128 = Rust_primitives.Arithmetic.pow_i128 x exp

let impl_i128__count_ones (x: i128) : u32 = Rust_primitives.Arithmetic.count_ones_i128 x

assume
val impl_i128__rotate_right': x: i128 -> n: u32 -> i128

unfold
let impl_i128__rotate_right = impl_i128__rotate_right'

assume
val impl_i128__rotate_left': x: i128 -> n: u32 -> i128

unfold
let impl_i128__rotate_left = impl_i128__rotate_left'

assume
val impl_i128__leading_zeros': x: i128 -> u32

unfold
let impl_i128__leading_zeros = impl_i128__leading_zeros'

assume
val impl_i128__ilog2': x: i128 -> u32

unfold
let impl_i128__ilog2 = impl_i128__ilog2'

assume
val impl_i128__from_str_radix': src: string -> radix: u32
  -> Core_models.Result.t_Result i128 Core_models.Num.Error.t_ParseIntError

unfold
let impl_i128__from_str_radix = impl_i128__from_str_radix'

assume
val impl_i128__from_be_bytes': bytes: t_Array i128 (mk_usize 16) -> i128

unfold
let impl_i128__from_be_bytes = impl_i128__from_be_bytes'

assume
val impl_i128__from_le_bytes': bytes: t_Array i128 (mk_usize 16) -> i128

unfold
let impl_i128__from_le_bytes = impl_i128__from_le_bytes'

assume
val impl_i128__to_be_bytes': bytes: i128 -> t_Array i128 (mk_usize 16)

unfold
let impl_i128__to_be_bytes = impl_i128__to_be_bytes'

assume
val impl_i128__to_le_bytes': bytes: i128 -> t_Array i128 (mk_usize 16)

unfold
let impl_i128__to_le_bytes = impl_i128__to_le_bytes'

let impl_i128__rem_euclid (x y: i128)
    : Prims.Pure i128 (requires y <>. mk_i128 0) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.rem_euclid_i128 x y

let impl_i128__abs (x: i128)
    : Prims.Pure bool (requires x >. impl_i128__MIN) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.abs_i128 x

let impl_isize__MIN: isize = Rust_primitives.Arithmetic.v_ISIZE_MIN

let impl_isize__MAX: isize = Rust_primitives.Arithmetic.v_ISIZE_MAX

let impl_isize__BITS: u32 = Rust_primitives.Arithmetic.v_SIZE_BITS

let impl_isize__wrapping_add (x y: isize) : isize =
  Rust_primitives.Arithmetic.wrapping_add_isize x y

let impl_isize__saturating_add (x y: isize) : isize =
  Rust_primitives.Arithmetic.saturating_add_isize x y

let impl_isize__overflowing_add (x y: isize) : (isize & bool) =
  Rust_primitives.Arithmetic.overflowing_add_isize x y

let impl_isize__wrapping_sub (x y: isize) : isize =
  Rust_primitives.Arithmetic.wrapping_sub_isize x y

let impl_isize__saturating_sub (x y: isize) : isize =
  Rust_primitives.Arithmetic.saturating_sub_isize x y

let impl_isize__overflowing_sub (x y: isize) : (isize & bool) =
  Rust_primitives.Arithmetic.overflowing_sub_isize x y

let impl_isize__wrapping_mul (x y: isize) : isize =
  Rust_primitives.Arithmetic.wrapping_mul_isize x y

let impl_isize__saturating_mul (x y: isize) : isize =
  Rust_primitives.Arithmetic.saturating_mul_isize x y

let impl_isize__overflowing_mul (x y: isize) : (isize & bool) =
  Rust_primitives.Arithmetic.overflowing_mul_isize x y

let impl_isize__pow (x: isize) (exp: u32) : isize = Rust_primitives.Arithmetic.pow_isize x exp

let impl_isize__count_ones (x: isize) : u32 = Rust_primitives.Arithmetic.count_ones_isize x

assume
val impl_isize__rotate_right': x: isize -> n: u32 -> isize

unfold
let impl_isize__rotate_right = impl_isize__rotate_right'

assume
val impl_isize__rotate_left': x: isize -> n: u32 -> isize

unfold
let impl_isize__rotate_left = impl_isize__rotate_left'

assume
val impl_isize__leading_zeros': x: isize -> u32

unfold
let impl_isize__leading_zeros = impl_isize__leading_zeros'

assume
val impl_isize__ilog2': x: isize -> u32

unfold
let impl_isize__ilog2 = impl_isize__ilog2'

assume
val impl_isize__from_str_radix': src: string -> radix: u32
  -> Core_models.Result.t_Result isize Core_models.Num.Error.t_ParseIntError

unfold
let impl_isize__from_str_radix = impl_isize__from_str_radix'

assume
val impl_isize__from_be_bytes': bytes: t_Array isize (mk_usize 0) -> isize

unfold
let impl_isize__from_be_bytes = impl_isize__from_be_bytes'

assume
val impl_isize__from_le_bytes': bytes: t_Array isize (mk_usize 0) -> isize

unfold
let impl_isize__from_le_bytes = impl_isize__from_le_bytes'

assume
val impl_isize__to_be_bytes': bytes: isize -> t_Array isize (mk_usize 0)

unfold
let impl_isize__to_be_bytes = impl_isize__to_be_bytes'

assume
val impl_isize__to_le_bytes': bytes: isize -> t_Array isize (mk_usize 0)

unfold
let impl_isize__to_le_bytes = impl_isize__to_le_bytes'

let impl_isize__rem_euclid (x y: isize)
    : Prims.Pure isize (requires y <>. mk_isize 0) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.rem_euclid_isize x y

let impl_isize__abs (x: isize)
    : Prims.Pure bool (requires x >. impl_isize__MIN) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.abs_isize x

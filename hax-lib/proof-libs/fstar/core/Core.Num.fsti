module Core.Num
open Rust_primitives

let impl_u8__MAX: u8 = mk_u8 (maxint u8_inttype)
let impl_u8__MIN: u8 = mk_u8 (minint u8_inttype)
let impl_u16__MAX: u16 = mk_u16 (maxint u16_inttype)
let impl_u16__MIN: u16 = mk_u16 (minint u16_inttype)
let impl_u32__MAX: u32 = mk_u32 (maxint u32_inttype)
let impl_u32__MIN: u32 = mk_u32 (minint u32_inttype)
let impl_u64__MAX: u64 = mk_u64 (maxint u64_inttype)
let impl_u64__MIN: u64 = mk_u64 (minint u64_inttype)
let impl_u128__MAX: u128 = mk_u128 (maxint u128_inttype)
let impl_u128__MIN: u128 = mk_u128 (minint u128_inttype)
let impl_usize__MAX: usize = mk_usize (maxint usize_inttype)

let impl_usize__MIN: usize = mk_usize (minint usize_inttype)
let impl_i8__MAX: i8 = mk_i8 (maxint i8_inttype)
let impl_i8__MIN: i8 = mk_i8 (minint i8_inttype)
let impl_i16__MAX: i16 = mk_i16 (maxint i16_inttype)
let impl_i16__MIN: i16 = mk_i16 (minint i16_inttype)
let impl_i32__MAX: i32 = mk_i32 (maxint i32_inttype)
let impl_i32__MIN: i32 = mk_i32 (minint i32_inttype)
let impl_i64__MAX: i64 = mk_i64 (maxint i64_inttype)
let impl_i64__MIN: i64 = mk_i64 (minint i64_inttype)
let impl_i128__MAX: i128 = mk_i128 (maxint i128_inttype)
let impl_i128__MIN: i128 = mk_i128 (minint i128_inttype)
let impl_isize__MAX: isize = mk_isize (maxint isize_inttype)
let impl_isize__MIN: isize = mk_isize (minint isize_inttype)

let impl_u8__BITS: u32 = mk_int 8
let impl_u16__BITS: u32 = mk_int 16
let impl_u32__BITS: u32 = mk_int 32
let impl_u64__BITS: u32 = mk_int 64
let impl_u128__BITS: u32 = mk_int 128
let impl_i8__BITS: u32 = mk_int 8
let impl_i16__BITS: u32 = mk_int 16
let impl_i32__BITS: u32 = mk_int 32
let impl_i64__BITS: u32 = mk_int 64
let impl_i128__BITS: u32 = mk_int 128



let impl_u8__wrapping_add: u8 -> u8 -> u8 = add_mod
let impl_u16__wrapping_add: u16 -> u16 ->  u16 = add_mod
let impl_u32__wrapping_add: u32 -> u32 -> u32 = add_mod
let impl_u64__wrapping_add: u64 -> u64 -> u64 = add_mod
let impl_u128__wrapping_add: u128 -> u128 -> u128 = add_mod
let impl_i8__wrapping_add: i8 -> i8 -> i8 = add_mod
let impl_i16__wrapping_add: i16 -> i16 ->  i16 = add_mod
let impl_i32__wrapping_add: i32 -> i32 -> i32 = add_mod
let impl_i64__wrapping_add: i64 -> i64 -> i64 = add_mod
let impl_i128__wrapping_add: i128 -> i128 -> i128 = add_mod

let impl_u8__saturating_add: u8 -> u8 -> u8 = add_sat
let impl_u16__saturating_add: u16 -> u16 ->  u16 = add_sat
let impl_u32__saturating_add: u32 -> u32 -> u32 = add_sat
let impl_u64__saturating_add: u64 -> u64 -> u64 = add_sat
let impl_u128__saturating_add: u128 -> u128 -> u128 = add_sat
let impl_i8__saturating_add: i8 -> i8 -> i8 = add_sat
let impl_i16__saturating_add: i16 -> i16 ->  i16 = add_sat
let impl_i32__saturating_add: i32 -> i32 -> i32 = add_sat
let impl_i64__saturating_add: i64 -> i64 -> i64 = add_sat
let impl_i128__saturating_add: i128 -> i128 -> i128 = add_sat


let impl_u8__wrapping_sub: u8 -> u8 -> u8 = sub_mod
let impl_u16__wrapping_sub: u16 -> u16 ->  u16 = sub_mod
let impl_u32__wrapping_sub: u32 -> u32 -> u32 = sub_mod
let impl_u64__wrapping_sub: u64 -> u64 -> u64 = sub_mod
let impl_u128__wrapping_sub: u128 -> u128 -> u128 = sub_mod
let impl_i8__wrapping_sub: i8 -> i8 -> i8 = sub_mod
let impl_i16__wrapping_sub: i16 -> i16 ->  i16 = sub_mod
let impl_i32__wrapping_sub: i32 -> i32 -> i32 = sub_mod
let impl_i64__wrapping_sub: i64 -> i64 -> i64 = sub_mod
let impl_i128__wrapping_sub: i128 -> i128 -> i128 = sub_mod


let impl_u8__saturating_sub: u8 -> u8 -> u8 = sub_sat
let impl_u16__saturating_sub: u16 -> u16 ->  u16 = sub_sat
let impl_u32__saturating_sub: u32 -> u32 -> u32 = sub_sat
let impl_u64__saturating_sub: u64 -> u64 -> u64 = sub_sat
let impl_u128__saturating_sub: u128 -> u128 -> u128 = sub_sat
let impl_i8__saturating_sub: i8 -> i8 -> i8 = sub_sat
let impl_i16__saturating_sub: i16 -> i16 ->  i16 = sub_sat
let impl_i32__saturating_sub: i32 -> i32 -> i32 = sub_sat
let impl_i64__saturating_sub: i64 -> i64 -> i64 = sub_sat
let impl_i128__saturating_sub: i128 -> i128 -> i128 = sub_sat

let impl_u8__rem_euclid (x: u8) (y: u8 {v y <> 0}): u8 = x %! y
let impl_u16__rem_euclid (x: u16) (y: u16 {v y <> 0}): u16 = x %! y
let impl_u32__rem_euclid (x: u32) (y: u32 {v y <> 0}): u32 = x %! y
let impl_u64__rem_euclid (x: u64) (y: u64 {v y <> 0}): u64 = x %! y
let impl_u128__rem_euclid (x: u128) (y: u128 {v y <> 0}): u128 = x %! y
let impl_usize__rem_euclid (x: usize) (y: usize {v y <> 0}): usize = x %! y
let impl_i8__rem_euclid (x: i8) (y: i8 {v y <> 0}): i8 = x %! y
let impl_i16__rem_euclid (x: i16) (y: i16 {v y <> 0}): i16 = x %! y
let impl_i32__rem_euclid (x: i32) (y: i32 {v y <> 0}): i32 = x %! y
let impl_i64__rem_euclid (x: i64) (y: i64 {v y <> 0}): i64 = x %! y
let impl_i128__rem_euclid (x: i128) (y: i128 {v y <> 0}): i128 = x %! y
let impl_isize__rem_euclid (x: isize) (y: isize {v y <> 0}): isize = x %! y



let impl_u8__overflowing_mul: u8 -> u8 -> u8 * bool = mul_overflow
let impl_u16__overflowing_mul: u16 -> u16 ->  u16 * bool = mul_overflow
let impl_u32__overflowing_mul: u32 -> u32 -> u32 * bool = mul_overflow
let impl_u64__overflowing_mul: u64 -> u64 -> u64 * bool = mul_overflow
let impl_u128__overflowing_mul: u128 -> u128 -> u128 * bool = mul_overflow
let impl_i8__overflowing_mul: i8 -> i8 -> i8 * bool = mul_overflow
let impl_i16__overflowing_mul: i16 -> i16 ->  i16 * bool = mul_overflow
let impl_i32__overflowing_mul: i32 -> i32 -> i32 * bool = mul_overflow
let impl_i64__overflowing_mul: i64 -> i64 -> i64 * bool = mul_overflow
let impl_i128__overflowing_mul: i128 -> i128 -> i128 * bool = mul_overflow

val impl_u16__to_be_bytes: u16 -> t_Array u8 (sz 2)
val impl_u16__from_be_bytes: t_Array u8 (sz 2) -> u16

let impl_i8__abs (a:i8{minint i8_inttype < v a}) : i8 = abs_int a
let impl_i16__abs (a:i16{minint i16_inttype < v a}) : i16 = abs_int a
let impl_i32__abs (a:i32{minint i32_inttype < v a}) : i32 = abs_int a
let impl_i64__abs (a:i64{minint i64_inttype < v a}) : i64 = abs_int a
let impl_i128__abs (a:i128{minint i128_inttype < v a}) : i128 = abs_int a


let impl_i16__wrapping_mul: i16 -> i16 -> i16 = mul_mod


val impl_u32__rotate_left: u32 -> u32 -> u32
val impl_u32__from_le_bytes: t_Array u8 (sz 4) -> u32
val impl_u32__from_be_bytes: t_Array u8 (sz 4) -> u32
val impl_u32__to_le_bytes: u32 -> t_Array u8 (sz 4)
val impl_u32__to_be_bytes: u32 -> t_Array u8 (sz 4)
val impl_u32__rotate_right: u32 -> u32 -> u32


val impl_u64__rotate_left: u32 -> u32 -> u32
val impl_u64__from_le_bytes: t_Array u8 (sz 8) -> u64
val impl_u64__from_be_bytes: t_Array u8 (sz 8) -> u64
val impl_u64__to_le_bytes: u64 -> t_Array u8 (sz 8)
val impl_u64__to_be_bytes: u64 -> t_Array u8 (sz 8)
val impl_u64__rotate_right: u64 -> u64 -> u64
let impl_u64__overflowing_sub (x y: u64): u64 * bool
  = let sub = v x - v y in
    let borrow = sub < 0 in
    let out = if borrow then pow2 64 + sub else sub in
    (mk_u64 out, borrow)

let impl_i64__wrapping_mul: i64 -> i64 -> i64 = mul_mod

val impl_u128__rotate_left: u128 -> u128 -> u128
val impl_u128__from_le_bytes: t_Array u8 (sz 16) -> u128
val impl_u128__from_be_bytes: t_Array u8 (sz 16) -> u128
val impl_u128__to_le_bytes: u128 -> t_Array u8 (sz 16)
val impl_u128__to_be_bytes: u128 -> t_Array u8 (sz 16)
val impl_u128__rotate_right: u128 -> u128 -> u128

val impl_u8__pow: u8 -> u32 -> u8
val impl_u16__pow (base: u16) (exponent: u32): result : u16 {v base == 2 /\ v exponent < 16 ==> result == mk_u16 (pow2 (v exponent))}
val impl_u32__pow (base: u32) (exponent: u32): result : u32 {v base == 2 /\ v exponent <= 16 ==> result == mk_u32 (pow2 (v exponent))}
val impl_u64__pow: u64 -> u32 -> u64
val impl_u128__pow: u128 -> u32 -> u128
val impl_i16__pow (base: i16) (exponent: u32): result: i16 {v base == 2 /\ v exponent < 15 ==> (Math.Lemmas.pow2_lt_compat 15 (v exponent); result == mk_i16 (pow2 (v exponent)))}
val impl_i32__pow (base: i32) (exponent: u32): result: i32 {v base == 2 /\ v exponent <= 16 ==> result == mk_i32 (pow2 (v exponent))}


val impl_u8__count_ones: u8 -> r:u32{v r <= 8}
val impl_i32__count_ones: i32 -> r:u32{v r <= 32}

val impl_u8__from_str_radix: string -> u32 -> Core.Result.t_Result u8 Core.Num.Error.t_ParseIntError

val impl_usize__ilog2: i32 -> u32 
val impl_usize__leading_zeros: usize -> u32

open Core.Ops.Arith
unfold instance add_assign_num_refined_refined t ($phi1 $phi2: int_t t -> bool)
  : t_AddAssign (x: int_t t {phi1 x}) (y: int_t t {phi2 y}) = {
    f_add_assign_pre = (fun (x: int_t t {phi1 x}) (y: int_t t {phi2 y}) -> phi1 (x +. y));
    f_add_assign_post = (fun x y r -> x +. y = r);
    f_add_assign = (fun x y -> x +. y);
  }
unfold instance add_assign_num_lhs_refined t ($phi1: int_t t -> bool)
  : t_AddAssign (x: int_t t {phi1 x}) (y: int_t t) = {
    f_add_assign_pre = (fun (x: int_t t {phi1 x}) (y: int_t t) -> phi1 (x +. y));
    f_add_assign_post = (fun x y r -> x +. y = r);
    f_add_assign = (fun x y -> x +. y);
  }
unfold instance add_assign_num_rhs_refined t ($phi1: int_t t -> bool)
  : t_AddAssign (x: int_t t) (y: int_t t {phi1 y}) = {
    f_add_assign_pre = (fun (x: int_t t) (y: int_t t {phi1 y}) -> true);
    f_add_assign_post = (fun x y r -> x +. y = r);
    f_add_assign = (fun x y -> x +. y);
  }
unfold instance add_assign_num t
  : t_AddAssign (x: int_t t) (y: int_t t) = {
    f_add_assign_pre = (fun (x: int_t t) (y: int_t t) -> true);
    f_add_assign_post = (fun x y r -> x +. y = r);
    f_add_assign = (fun x y -> x +. y);
  }

unfold instance sub_assign_num_refined_refined t ($phi1 $phi2: int_t t -> bool)
  : t_SubAssign (x: int_t t {phi1 x}) (y: int_t t {phi2 y}) = {
    f_sub_assign_pre = (fun (x: int_t t {phi1 x}) (y: int_t t {phi2 y}) -> phi1 (x -. y));
    f_sub_assign_post = (fun x y r -> x -. y = r);
    f_sub_assign = (fun x y -> x -. y);
  }
unfold instance sub_assign_num_lhs_refined t ($phi1: int_t t -> bool)
  : t_SubAssign (x: int_t t {phi1 x}) (y: int_t t) = {
    f_sub_assign_pre = (fun (x: int_t t {phi1 x}) (y: int_t t) -> phi1 (x -. y));
    f_sub_assign_post = (fun x y r -> x -. y = r);
    f_sub_assign = (fun x y -> x -. y);
  }
unfold instance sub_assign_num_rhs_refined t ($phi1: int_t t -> bool)
  : t_SubAssign (x: int_t t) (y: int_t t {phi1 y}) = {
    f_sub_assign_pre = (fun (x: int_t t) (y: int_t t {phi1 y}) -> true);
    f_sub_assign_post = (fun x y r -> x -. y = r);
    f_sub_assign = (fun x y -> x -. y);
  }
unfold instance sub_assign_num t
  : t_SubAssign (x: int_t t) (y: int_t t) = {
    f_sub_assign_pre = (fun (x: int_t t) (y: int_t t) -> true);
    f_sub_assign_post = (fun x y r -> x -. y = r);
    f_sub_assign = (fun x y -> x -. y);
  }

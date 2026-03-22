module Rust_primitives.Arithmetic

open FStar.Mul
open Rust_primitives.Integers
open Rust_primitives.BitOps

(* Generic helpers *)

let overflowing_add_unsigned (#t:inttype{unsigned t}) (x y: int_t t): int_t t & bool =
  (add_mod x y, v x + v y > maxint t)

let overflowing_add_signed (#t:inttype{signed t}) (x y: int_t t): int_t t & bool =
  (add_mod x y, v x + v y > maxint t || v x + v y < minint t)

let overflowing_sub_signed (#t:inttype{signed t}) (x y: int_t t): int_t t & bool =
  (sub_mod x y, v x - v y > maxint t || v x - v y < minint t)

let saturating_mul_generic (#t:inttype) (x y: int_t t): int_t t =
  let p = v x * v y in
  if p > maxint t then mk_int (maxint t)
  else if p < minint t then mk_int (minint t)
  else mk_int p

let pow_generic (#t:inttype) (x: int_t t) (y: u32): int_t t =
  mk_int (pow_nat (v x) (v y) @%. t)

let count_ones_generic (#t:inttype) (x: int_t t): (r:u32{v r <= bits t}) =
  mk_u32 (count_ones_nat (to_uint t (v x)) (bits t))

let abs_signed (#t:inttype{signed t}) (x: int_t t): int_t t =
  if v x >= 0 then x
  else if v x = minint t then x (* wrapping: abs(MIN) = MIN *)
  else mk_int (0 - v x)

(* ---- u8 ---- *)
let wrapping_add_u8 : u8 -> u8 -> u8 = add_mod
let saturating_add_u8 : u8 -> u8 -> u8 = add_sat
let overflowing_add_u8 : u8 -> u8 -> u8 & bool = overflowing_add_unsigned
let wrapping_sub_u8 : u8 -> u8 -> u8 = sub_mod
let saturating_sub_u8 : u8 -> u8 -> u8 = sub_sat
let overflowing_sub_u8 (x y: u8): u8 & bool
  = let sub = v x - v y in
    let borrow = sub < 0 in
    let out = if borrow then pow2 8 + sub else sub in
    (mk_u8 out, borrow)
let wrapping_mul_u8 : u8 -> u8 -> u8 = mul_mod
let saturating_mul_u8 : u8 -> u8 -> u8 = saturating_mul_generic
let overflowing_mul_u8 : u8 -> u8 -> u8 & bool = mul_overflow
let rem_euclid_u8 (x: u8) (y: u8 {v y <> 0}): u8 = x %! y
let pow_u8 : u8 -> u32 -> u8 = pow_generic
let count_ones_u8 : u8 -> r:u32{v r <= 8} = count_ones_generic

(* ---- u16 ---- *)
let wrapping_add_u16 : u16 -> u16 -> u16 = add_mod
let saturating_add_u16 : u16 -> u16 -> u16 = add_sat
let overflowing_add_u16 : u16 -> u16 -> u16 & bool = overflowing_add_unsigned
let wrapping_sub_u16 : u16 -> u16 -> u16 = sub_mod
let saturating_sub_u16 : u16 -> u16 -> u16 = sub_sat
let overflowing_sub_u16 (x y: u16): u16 & bool
  = let sub = v x - v y in
    let borrow = sub < 0 in
    let out = if borrow then pow2 16 + sub else sub in
    (mk_u16 out, borrow)
let wrapping_mul_u16 : u16 -> u16 -> u16 = mul_mod
let saturating_mul_u16 : u16 -> u16 -> u16 = saturating_mul_generic
let overflowing_mul_u16 : u16 -> u16 -> u16 & bool = mul_overflow
let rem_euclid_u16 (x: u16) (y: u16 {v y <> 0}): u16 = x %! y
let pow_u16 : u16 -> u32 -> u16 = pow_generic
let count_ones_u16 : u16 -> r:u32{v r <= 16} = count_ones_generic

(* ---- u32 ---- *)
let wrapping_add_u32 : u32 -> u32 -> u32 = add_mod
let saturating_add_u32 : u32 -> u32 -> u32 = add_sat
let overflowing_add_u32 : u32 -> u32 -> u32 & bool = overflowing_add_unsigned
let wrapping_sub_u32 : u32 -> u32 -> u32 = sub_mod
let saturating_sub_u32 : u32 -> u32 -> u32 = sub_sat
let overflowing_sub_u32 (x y: u32): u32 & bool
  = let sub = v x - v y in
    let borrow = sub < 0 in
    let out = if borrow then pow2 32 + sub else sub in
    (mk_u32 out, borrow)
let wrapping_mul_u32 : u32 -> u32 -> u32 = mul_mod
let saturating_mul_u32 : u32 -> u32 -> u32 = saturating_mul_generic
let overflowing_mul_u32 : u32 -> u32 -> u32 & bool = mul_overflow
let rem_euclid_u32 (x: u32) (y: u32 {v y <> 0}): u32 = x %! y
let pow_u32 : u32 -> u32 -> u32 = pow_generic
let count_ones_u32 : u32 -> r:u32{v r <= 32} = count_ones_generic

(* ---- u64 ---- *)
let wrapping_add_u64 : u64 -> u64 -> u64 = add_mod
let saturating_add_u64 : u64 -> u64 -> u64 = add_sat
let overflowing_add_u64 : u64 -> u64 -> u64 & bool = overflowing_add_unsigned
let wrapping_sub_u64 : u64 -> u64 -> u64 = sub_mod
let saturating_sub_u64 : u64 -> u64 -> u64 = sub_sat
let overflowing_sub_u64 (x y: u64): u64 & bool
  = let sub = v x - v y in
    let borrow = sub < 0 in
    let out = if borrow then pow2 64 + sub else sub in
    (mk_u64 out, borrow)
let wrapping_mul_u64 : u64 -> u64 -> u64 = mul_mod
let saturating_mul_u64 : u64 -> u64 -> u64 = saturating_mul_generic
let overflowing_mul_u64 : u64 -> u64 -> u64 & bool = mul_overflow
let rem_euclid_u64 (x: u64) (y: u64 {v y <> 0}): u64 = x %! y
let pow_u64 : u64 -> u32 -> u64 = pow_generic
let count_ones_u64 : u64 -> r:u32{v r <= 64} = count_ones_generic

(* ---- u128 ---- *)
let wrapping_add_u128 : u128 -> u128 -> u128 = add_mod
let saturating_add_u128 : u128 -> u128 -> u128 = add_sat
let overflowing_add_u128 : u128 -> u128 -> u128 & bool = overflowing_add_unsigned
let wrapping_sub_u128 : u128 -> u128 -> u128 = sub_mod
let saturating_sub_u128 : u128 -> u128 -> u128 = sub_sat
let overflowing_sub_u128 (x y: u128): u128 & bool
  = let sub = v x - v y in
    let borrow = sub < 0 in
    let out = if borrow then pow2 128 + sub else sub in
    (mk_u128 out, borrow)
let wrapping_mul_u128 : u128 -> u128 -> u128 = mul_mod
let saturating_mul_u128 : u128 -> u128 -> u128 = saturating_mul_generic
let overflowing_mul_u128 : u128 -> u128 -> u128 & bool = mul_overflow
let rem_euclid_u128 (x: u128) (y: u128 {v y <> 0}): u128 = x %! y
let pow_u128 : u128 -> u32 -> u128 = pow_generic
let count_ones_u128 : u128 -> r:u32{v r <= 128} = count_ones_generic

(* ---- usize ---- *)
let wrapping_add_usize : usize -> usize -> usize = add_mod
let saturating_add_usize : usize -> usize -> usize = add_sat
let overflowing_add_usize : usize -> usize -> usize & bool = overflowing_add_unsigned
let wrapping_sub_usize : usize -> usize -> usize = sub_mod
let saturating_sub_usize : usize -> usize -> usize = sub_sat
let overflowing_sub_usize (x y: usize): usize & bool
  = let sub = v x - v y in
    let borrow = sub < 0 in
    let out = if borrow then pow2 size_bits + sub else sub in
    (mk_usize out, borrow)
let wrapping_mul_usize : usize -> usize -> usize = mul_mod
let saturating_mul_usize : usize -> usize -> usize = saturating_mul_generic
let overflowing_mul_usize : usize -> usize -> usize & bool = mul_overflow
let rem_euclid_usize (x: usize) (y: usize {v y <> 0}): usize = x %! y
let pow_usize : usize -> u32 -> usize = pow_generic
let count_ones_usize : usize -> r:u32{v r <= size_bits} = count_ones_generic

(* ---- i8 ---- *)
let wrapping_add_i8 : i8 -> i8 -> i8 = add_mod
let saturating_add_i8 : i8 -> i8 -> i8 = add_sat
let overflowing_add_i8 : i8 -> i8 -> i8 & bool = overflowing_add_signed
let wrapping_sub_i8 : i8 -> i8 -> i8 = sub_mod
let saturating_sub_i8 : i8 -> i8 -> i8 = sub_sat
let overflowing_sub_i8 (x y: i8): i8 & bool = overflowing_sub_signed x y
let wrapping_mul_i8 : i8 -> i8 -> i8 = mul_mod
let saturating_mul_i8 : i8 -> i8 -> i8 = saturating_mul_generic
let overflowing_mul_i8 : i8 -> i8 -> i8 & bool = mul_overflow
let rem_euclid_i8 (x: i8) (y: i8 {v y <> 0}): i8 = x %! y
let pow_i8 : i8 -> u32 -> i8 = pow_generic
let count_ones_i8 : i8 -> r:u32{v r <= 8} = count_ones_generic
let abs_i8 : i8 -> i8 = abs_signed

(* ---- i16 ---- *)
let wrapping_add_i16 : i16 -> i16 -> i16 = add_mod
let saturating_add_i16 : i16 -> i16 -> i16 = add_sat
let overflowing_add_i16 : i16 -> i16 -> i16 & bool = overflowing_add_signed
let wrapping_sub_i16 : i16 -> i16 -> i16 = sub_mod
let saturating_sub_i16 : i16 -> i16 -> i16 = sub_sat
let overflowing_sub_i16 (x y: i16): i16 & bool = overflowing_sub_signed x y
let wrapping_mul_i16 : i16 -> i16 -> i16 = mul_mod
let saturating_mul_i16 : i16 -> i16 -> i16 = saturating_mul_generic
let overflowing_mul_i16 : i16 -> i16 -> i16 & bool = mul_overflow
let rem_euclid_i16 (x: i16) (y: i16 {v y <> 0}): i16 = x %! y
let pow_i16 : i16 -> u32 -> i16 = pow_generic
let count_ones_i16 : i16 -> r:u32{v r <= 16} = count_ones_generic
let abs_i16 : i16 -> i16 = abs_signed

(* ---- i32 ---- *)
let wrapping_add_i32 : i32 -> i32 -> i32 = add_mod
let saturating_add_i32 : i32 -> i32 -> i32 = add_sat
let overflowing_add_i32 : i32 -> i32 -> i32 & bool = overflowing_add_signed
let wrapping_sub_i32 : i32 -> i32 -> i32 = sub_mod
let saturating_sub_i32 : i32 -> i32 -> i32 = sub_sat
let overflowing_sub_i32 (x y: i32): i32 & bool = overflowing_sub_signed x y
let wrapping_mul_i32 : i32 -> i32 -> i32 = mul_mod
let saturating_mul_i32 : i32 -> i32 -> i32 = saturating_mul_generic
let overflowing_mul_i32 : i32 -> i32 -> i32 & bool = mul_overflow
let rem_euclid_i32 (x: i32) (y: i32 {v y <> 0}): i32 = x %! y
let pow_i32 : i32 -> u32 -> i32 = pow_generic
let count_ones_i32 : i32 -> r:u32{v r <= 32} = count_ones_generic
let abs_i32 : i32 -> i32 = abs_signed

(* ---- i64 ---- *)
let wrapping_add_i64 : i64 -> i64 -> i64 = add_mod
let saturating_add_i64 : i64 -> i64 -> i64 = add_sat
let overflowing_add_i64 : i64 -> i64 -> i64 & bool = overflowing_add_signed
let wrapping_sub_i64 : i64 -> i64 -> i64 = sub_mod
let saturating_sub_i64 : i64 -> i64 -> i64 = sub_sat
let overflowing_sub_i64 (x y: i64): i64 & bool = overflowing_sub_signed x y
let wrapping_mul_i64 : i64 -> i64 -> i64 = mul_mod
let saturating_mul_i64 : i64 -> i64 -> i64 = saturating_mul_generic
let overflowing_mul_i64 : i64 -> i64 -> i64 & bool = mul_overflow
let rem_euclid_i64 (x: i64) (y: i64 {v y <> 0}): i64 = x %! y
let pow_i64 : i64 -> u32 -> i64 = pow_generic
let count_ones_i64 : i64 -> r:u32{v r <= 64} = count_ones_generic
let abs_i64 : i64 -> i64 = abs_signed

(* ---- i128 ---- *)
let wrapping_add_i128 : i128 -> i128 -> i128 = add_mod
let saturating_add_i128 : i128 -> i128 -> i128 = add_sat
let overflowing_add_i128 : i128 -> i128 -> i128 & bool = overflowing_add_signed
let wrapping_sub_i128 : i128 -> i128 -> i128 = sub_mod
let saturating_sub_i128 : i128 -> i128 -> i128 = sub_sat
let overflowing_sub_i128 (x y: i128): i128 & bool = overflowing_sub_signed x y
let wrapping_mul_i128 : i128 -> i128 -> i128 = mul_mod
let saturating_mul_i128 : i128 -> i128 -> i128 = saturating_mul_generic
let overflowing_mul_i128 : i128 -> i128 -> i128 & bool = mul_overflow
let rem_euclid_i128 (x: i128) (y: i128 {v y <> 0}): i128 = x %! y
let pow_i128 : i128 -> u32 -> i128 = pow_generic
let count_ones_i128 : i128 -> r:u32{v r <= 128} = count_ones_generic
let abs_i128 : i128 -> i128 = abs_signed

(* ---- isize ---- *)
let wrapping_add_isize : isize -> isize -> isize = add_mod
let saturating_add_isize : isize -> isize -> isize = add_sat
let overflowing_add_isize : isize -> isize -> isize & bool = overflowing_add_signed
let wrapping_sub_isize : isize -> isize -> isize = sub_mod
let saturating_sub_isize : isize -> isize -> isize = sub_sat
let overflowing_sub_isize (x y: isize): isize & bool = overflowing_sub_signed x y
let wrapping_mul_isize : isize -> isize -> isize = mul_mod
let saturating_mul_isize : isize -> isize -> isize = saturating_mul_generic
let overflowing_mul_isize : isize -> isize -> isize & bool = mul_overflow
let rem_euclid_isize (x: isize) (y: isize {v y <> 0}): isize = x %! y
let pow_isize : isize -> u32 -> isize = pow_generic
let count_ones_isize : isize -> r:u32{v r <= size_bits} = count_ones_generic
let abs_isize : isize -> isize = abs_signed

let v_USIZE_MAX = mk_usize max_usize
let v_ISIZE_MAX = mk_isize max_isize
let v_ISIZE_MIN = mk_isize (minint ISIZE)
let v_SIZE_BITS = mk_u32 size_bits

let neg #t x = zero #t -! x

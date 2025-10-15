module Rust_primitives.Arithmetic

open FStar.Mul
open Rust_primitives.Integers

let wrapping_add_u8 : u8 -> u8 -> u8 = add_mod
let saturating_add_u8 : u8 -> u8 -> u8 = add_sat
val overflowing_add_u8 : u8 -> u8 -> u8 & bool
let wrapping_sub_u8 : u8 -> u8 -> u8 = sub_mod
let saturating_sub_u8 : u8 -> u8 -> u8 = sub_sat
let overflowing_sub_u8 (x y: u8): u8 & bool
  = let sub = v x - v y in
    let borrow = sub < 0 in
    let out = if borrow then pow2 8 + sub else sub in
    (mk_u8 out, borrow)
let wrapping_mul_u8 : u8 -> u8 -> u8 = mul_mod
val saturating_mul_u8 : u8 -> u8 -> u8
let overflowing_mul_u8 : u8 -> u8 -> u8 & bool = mul_overflow
let rem_euclid_u8 (x: u8) (y: u8 {v y <> 0}): u8 = x %! y
val pow_u8 : u8 -> u32 -> u8
val count_ones_u8 : u8 -> r:u32{v r <= 8}

let wrapping_add_u16 : u16 -> u16 -> u16 = add_mod
let saturating_add_u16 : u16 -> u16 -> u16 = add_sat
val overflowing_add_u16 : u16 -> u16 -> u16 & bool
let wrapping_sub_u16 : u16 -> u16 -> u16 = sub_mod
let saturating_sub_u16 : u16 -> u16 -> u16 = sub_sat
let overflowing_sub_u16 (x y: u16): u16 & bool
  = let sub = v x - v y in
    let borrow = sub < 0 in
    let out = if borrow then pow2 16 + sub else sub in
    (mk_u16 out, borrow)
let wrapping_mul_u16 : u16 -> u16 -> u16 = mul_mod
val saturating_mul_u16 : u16 -> u16 -> u16
let overflowing_mul_u16 : u16 -> u16 -> u16 & bool = mul_overflow
let rem_euclid_u16 (x: u16) (y: u16 {v y <> 0}): u16 = x %! y
val pow_u16 : x:u16 -> y:u32 -> result : u16 {v x == 2 /\ v y < 16 ==> result == mk_u16 (pow2 (v y))}
val count_ones_u16 : u16 -> r:u32{v r <= 16}

let wrapping_add_u32 : u32 -> u32 -> u32 = add_mod
let saturating_add_u32 : u32 -> u32 -> u32 = add_sat
val overflowing_add_u32 : u32 -> u32 -> u32 & bool
let wrapping_sub_u32 : u32 -> u32 -> u32 = sub_mod
let saturating_sub_u32 : u32 -> u32 -> u32 = sub_sat
let overflowing_sub_u32 (x y: u32): u32 & bool
  = let sub = v x - v y in
    let borrow = sub < 0 in
    let out = if borrow then pow2 32 + sub else sub in
    (mk_u32 out, borrow)
let wrapping_mul_u32 : u32 -> u32 -> u32 = mul_mod
val saturating_mul_u32 : u32 -> u32 -> u32
let overflowing_mul_u32 : u32 -> u32 -> u32 & bool = mul_overflow
let rem_euclid_u32 (x: u32) (y: u32 {v y <> 0}): u32 = x %! y
val pow_u32 : x:u32 -> y:u32 -> result : u32 {v x == 2 /\ v y <= 16 ==> result == mk_u32 (pow2 (v y))}
val count_ones_u32 : u32 -> r:u32{v r <= 32}

let wrapping_add_u64 : u64 -> u64 -> u64 = add_mod
let saturating_add_u64 : u64 -> u64 -> u64 = add_sat
val overflowing_add_u64 : u64 -> u64 -> u64 & bool
let wrapping_sub_u64 : u64 -> u64 -> u64 = sub_mod
let saturating_sub_u64 : u64 -> u64 -> u64 = sub_sat
let overflowing_sub_u64 (x y: u64): u64 & bool
  = let sub = v x - v y in
    let borrow = sub < 0 in
    let out = if borrow then pow2 64 + sub else sub in
    (mk_u64 out, borrow)
let wrapping_mul_u64 : u64 -> u64 -> u64 = mul_mod
val saturating_mul_u64 : u64 -> u64 -> u64
let overflowing_mul_u64 : u64 -> u64 -> u64 & bool = mul_overflow
let rem_euclid_u64 (x: u64) (y: u64 {v y <> 0}): u64 = x %! y
val pow_u64 : u64 -> u32 -> u64
val count_ones_u64 : u64 -> r:u32{v r <= 64}

let wrapping_add_u128 : u128 -> u128 -> u128 = add_mod
let saturating_add_u128 : u128 -> u128 -> u128 = add_sat
val overflowing_add_u128 : u128 -> u128 -> u128 & bool
let wrapping_sub_u128 : u128 -> u128 -> u128 = sub_mod
let saturating_sub_u128 : u128 -> u128 -> u128 = sub_sat
let overflowing_sub_u128 (x y: u128): u128 & bool
  = let sub = v x - v y in
    let borrow = sub < 0 in
    let out = if borrow then pow2 128 + sub else sub in
    (mk_u128 out, borrow)
let wrapping_mul_u128 : u128 -> u128 -> u128 = mul_mod
val saturating_mul_u128 : u128 -> u128 -> u128
let overflowing_mul_u128 : u128 -> u128 -> u128 & bool = mul_overflow
let rem_euclid_u128 (x: u128) (y: u128 {v y <> 0}): u128 = x %! y
val pow_u128 : u128 -> u32 -> u128
val count_ones_u128 : u128 -> r:u32{v r <= 128}

let wrapping_add_usize : usize -> usize -> usize = add_mod
let saturating_add_usize : usize -> usize -> usize = add_sat
val overflowing_add_usize : usize -> usize -> usize & bool
let wrapping_sub_usize : usize -> usize -> usize = sub_mod
let saturating_sub_usize : usize -> usize -> usize = sub_sat
let overflowing_sub_usize (x y: usize): usize & bool
  = let sub = v x - v y in
    let borrow = sub < 0 in
    let out = if borrow then pow2 size_bits + sub else sub in
    (mk_usize out, borrow)
let wrapping_mul_usize : usize -> usize -> usize = mul_mod
val saturating_mul_usize : usize -> usize -> usize
let overflowing_mul_usize : usize -> usize -> usize & bool = mul_overflow
let rem_euclid_usize (x: usize) (y: usize {v y <> 0}): usize = x %! y
val pow_usize : usize -> u32 -> usize
val count_ones_usize : usize -> r:u32{v r <= size_bits}

let wrapping_add_i8 : i8 -> i8 -> i8 = add_mod
let saturating_add_i8 : i8 -> i8 -> i8 = add_sat
val overflowing_add_i8 : i8 -> i8 -> i8 & bool
let wrapping_sub_i8 : i8 -> i8 -> i8 = sub_mod
let saturating_sub_i8 : i8 -> i8 -> i8 = sub_sat
val overflowing_sub_i8 (x y: i8): i8 & bool
let wrapping_mul_i8 : i8 -> i8 -> i8 = mul_mod
val saturating_mul_i8 : i8 -> i8 -> i8
let overflowing_mul_i8 : i8 -> i8 -> i8 & bool = mul_overflow
let rem_euclid_i8 (x: i8) (y: i8 {v y <> 0}): i8 = x %! y
val pow_i8 : i8 -> u32 -> i8
val count_ones_i8 : i8 -> r:u32{v r <= 8}
val abs_i8 : i8 -> i8

let wrapping_add_i16 : i16 -> i16 -> i16 = add_mod
let saturating_add_i16 : i16 -> i16 -> i16 = add_sat
val overflowing_add_i16 : i16 -> i16 -> i16 & bool
let wrapping_sub_i16 : i16 -> i16 -> i16 = sub_mod
let saturating_sub_i16 : i16 -> i16 -> i16 = sub_sat
val overflowing_sub_i16 (x y: i16): i16 & bool
let wrapping_mul_i16 : i16 -> i16 -> i16 = mul_mod
val saturating_mul_i16 : i16 -> i16 -> i16
let overflowing_mul_i16 : i16 -> i16 -> i16 & bool = mul_overflow
let rem_euclid_i16 (x: i16) (y: i16 {v y <> 0}): i16 = x %! y
val pow_i16 : x: i16 -> y:u32 -> result: i16 {v x == 2 /\ v y < 15 ==> (Math.Lemmas.pow2_lt_compat 15 (v y); result == mk_i16 (pow2 (v y)))}
val count_ones_i16 : i16 -> r:u32{v r <= 16}
val abs_i16 : i16 -> i16

let wrapping_add_i32 : i32 -> i32 -> i32 = add_mod
let saturating_add_i32 : i32 -> i32 -> i32 = add_sat
val overflowing_add_i32 : i32 -> i32 -> i32 & bool
let wrapping_sub_i32 : i32 -> i32 -> i32 = sub_mod
let saturating_sub_i32 : i32 -> i32 -> i32 = sub_sat
val overflowing_sub_i32 (x y: i32): i32 & bool
let wrapping_mul_i32 : i32 -> i32 -> i32 = mul_mod
val saturating_mul_i32 : i32 -> i32 -> i32
let overflowing_mul_i32 : i32 -> i32 -> i32 & bool = mul_overflow
let rem_euclid_i32 (x: i32) (y: i32 {v y <> 0}): i32 = x %! y
val pow_i32 : x : i32 -> y:u32 -> result: i32 {v x == 2 /\ v y <= 16 ==> result == mk_i32 (pow2 (v y))}
val count_ones_i32 : i32 -> r:u32{v r <= 32}
val abs_i32 : i32 -> i32

let wrapping_add_i64 : i64 -> i64 -> i64 = add_mod
let saturating_add_i64 : i64 -> i64 -> i64 = add_sat
val overflowing_add_i64 : i64 -> i64 -> i64 & bool
let wrapping_sub_i64 : i64 -> i64 -> i64 = sub_mod
let saturating_sub_i64 : i64 -> i64 -> i64 = sub_sat
val overflowing_sub_i64 (x y: i64): i64 & bool
let wrapping_mul_i64 : i64 -> i64 -> i64 = mul_mod
val saturating_mul_i64 : i64 -> i64 -> i64
let overflowing_mul_i64 : i64 -> i64 -> i64 & bool = mul_overflow
let rem_euclid_i64 (x: i64) (y: i64 {v y <> 0}): i64 = x %! y
val pow_i64 : i64 -> u32 -> i64
val count_ones_i64 : i64 -> r:u32{v r <= 64}
val abs_i64 : i64 -> i64

let wrapping_add_i128 : i128 -> i128 -> i128 = add_mod
let saturating_add_i128 : i128 -> i128 -> i128 = add_sat
val overflowing_add_i128 : i128 -> i128 -> i128 & bool
let wrapping_sub_i128 : i128 -> i128 -> i128 = sub_mod
let saturating_sub_i128 : i128 -> i128 -> i128 = sub_sat
val overflowing_sub_i128 (x y: i128): i128 & bool
let wrapping_mul_i128 : i128 -> i128 -> i128 = mul_mod
val saturating_mul_i128 : i128 -> i128 -> i128
let overflowing_mul_i128 : i128 -> i128 -> i128 & bool = mul_overflow
let rem_euclid_i128 (x: i128) (y: i128 {v y <> 0}): i128 = x %! y
val pow_i128 : i128 -> u32 -> i128
val count_ones_i128 : i128 -> r:u32{v r <= 128}
val abs_i128 : i128 -> i128

let wrapping_add_isize : isize -> isize -> isize = add_mod
let saturating_add_isize : isize -> isize -> isize = add_sat
val overflowing_add_isize : isize -> isize -> isize & bool
let wrapping_sub_isize : isize -> isize -> isize = sub_mod
let saturating_sub_isize : isize -> isize -> isize = sub_sat
val overflowing_sub_isize (x y: isize): isize & bool
let wrapping_mul_isize : isize -> isize -> isize = mul_mod
val saturating_mul_isize : isize -> isize -> isize
let overflowing_mul_isize : isize -> isize -> isize & bool = mul_overflow
let rem_euclid_isize (x: isize) (y: isize {v y <> 0}): isize = x %! y
val pow_isize : isize -> u32 -> isize
val count_ones_isize : isize -> r:u32{v r <= size_bits}
val abs_isize : isize -> isize

let v_USIZE_MAX = mk_usize max_usize
let v_ISIZE_MAX = mk_isize max_isize
let v_ISIZE_MIN = mk_isize (minint ISIZE)
let v_SIZE_BITS = mk_u32 size_bits

let neg #t x = zero #t -! x

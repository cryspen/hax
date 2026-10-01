//! Tests for `hax_lib`
//!
//! Test the extractions of `hax_lib::int` / `hax_lib::prop` / `hax_lib::abstraction` operations.
#![allow(dead_code, unused_variables)]

use hax_lib::*;

// ============================ hax_lib::int ============================

// --- arithmetic operators: + - * / and unary neg ---
#[hax_lib::ensures(|r| r.to_int() == a.to_int() + b.to_int() * int!(0) - b.to_int() * int!(0) / int!(1))]
fn int_arith(a: u32, b: u32) -> u32 {
    a
}

#[hax_lib::ensures(|r| r.to_int() == a.to_int() && -(a.to_int()) == int!(0) - a.to_int())]
fn int_neg(a: i32) -> i32 {
    a
}

// --- inherent methods: rem_euclid, pow2, and the `int!` literal macro ---
#[hax_lib::ensures(|r| r.to_int().rem_euclid(b.to_int()) == a.to_int().rem_euclid(b.to_int()))]
fn int_rem_euclid(a: u32, b: u32) -> u32 {
    a
}

#[hax_lib::ensures(|r| r.to_int() == a.to_int() + int!(2).pow2() - int!(4))]
fn int_pow2(a: u32) -> u32 {
    a
}

// --- comparison: ==, <, <=, >, >= and Ord::cmp ---
#[hax_lib::ensures(|r| (a.to_int() == b.to_int())
    || (a.to_int() < b.to_int()) || (a.to_int() <= b.to_int())
    || (a.to_int() > b.to_int()) || (a.to_int() >= b.to_int()))]
fn int_compare(a: u32, b: u32) -> u32 {
    a
}

#[hax_lib::ensures(|r| r.to_int().cmp(&a.to_int()).is_eq())]
fn int_ord_cmp(a: u32, b: u32) -> u32 {
    a
}

// ==================== hax_lib::abstraction ====================
//
// `lift` (machine -> Int) and the `Int::to_*` concretizations (Int -> machine)

macro_rules! exercise_absconc {
    ($($fn:ident $t:ty => $to:ident);* $(;)?) => {
        $(
            #[hax_lib::ensures(|r| a.lift() == r.to_int() && a.to_int().$to() == r)]
            fn $fn(a: $t) -> $t { a }
        )*
    };
}

exercise_absconc! {
    absconc_u8    u8    => to_u8;
    absconc_u16   u16   => to_u16;
    absconc_u32   u32   => to_u32;
    absconc_u64   u64   => to_u64;
    absconc_u128  u128  => to_u128;
    absconc_usize usize => to_usize;
    absconc_i8    i8    => to_i8;
    absconc_i16   i16   => to_i16;
    absconc_i32   i32   => to_i32;
    absconc_i64   i64   => to_i64;
    absconc_i128  i128  => to_i128;
    absconc_isize isize => to_isize;
}

// ============================ hax_lib::prop ============================

// --- quantifiers and free functions ---
#[hax_lib::requires(forall(|i: u8| implies(i < a, i < 100)))]
fn prop_forall(a: u8) -> u8 {
    a
}

#[hax_lib::requires(exists(|i: u32| i == a))]
fn prop_exists(a: u32) -> u32 {
    a
}

#[hax_lib::requires(implies(a > 10, a < 100))]
fn prop_implies_free(a: u32) -> u32 {
    a
}

#[hax_lib::requires(eq(a, a))]
fn prop_eq_free(a: u32) -> u32 {
    a
}

// --- `Prop` methods: to_prop, and, or, not, eq, ne, implies, from_bool ---
#[hax_lib::requires((a < 50).to_prop().and(b < 50).or(a == b).not())]
fn prop_and_or_not(a: u32, b: u32) -> u32 {
    a
}

#[hax_lib::requires((a > 0).to_prop().eq(a >= 1))]
fn prop_eq_method(a: u32) -> u32 {
    a
}

#[hax_lib::requires((a > 0).to_prop().ne(a == 0))]
fn prop_ne_method(a: u32) -> u32 {
    a
}

#[hax_lib::requires((a > 10).to_prop().implies(a > 5))]
fn prop_implies_method(a: u32) -> u32 {
    a
}

#[hax_lib::requires(Prop::from_bool(a < 100))]
fn prop_from_bool(a: u32) -> u32 {
    a
}

// --- operators on `Prop`: `&` (BitAnd), `|` (BitOr), `!` (Not) ---
#[hax_lib::requires(Prop::from_bool(a < 50) & (b < 50) | (a == b))]
fn prop_bitand_bitor(a: u32, b: u32) -> u32 {
    a
}

#[hax_lib::requires(!(a == 0).to_prop())]
fn prop_not_operator(a: u32) -> u32 {
    a
}

// --- `bool`'s `Abstraction::lift` (-> Prop) and the monomorphic constructors ---
#[hax_lib::requires(true.lift())]
fn prop_lift_bool(a: u32) -> u32 {
    a
}

#[hax_lib::requires(hax_lib::prop::constructors::and(
    hax_lib::prop::constructors::from_bool(a < 100),
    hax_lib::prop::constructors::or(
        hax_lib::prop::constructors::not(hax_lib::prop::constructors::from_bool(a == 0)),
        hax_lib::prop::constructors::ne(a, 0u32))))]
fn prop_constructors(a: u32) -> u32 {
    a
}

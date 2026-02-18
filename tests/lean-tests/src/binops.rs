//! Tests known binops
#![allow(dead_code)]

fn noop (x: i32) -> i32 { x }

/////////////////////
// UNARY FUNCTIONS //
/////////////////////

fn neg_int (x: i32) -> i32 { -x }

fn not_int (x: i32) -> i32 { !x }

fn not_bool (x: bool) -> bool { !x }

fn index (x: [i32; 1]) -> i32 { x[0] }

//////////////////////
// BINARY FUNCTIONS //
//////////////////////

fn add_int (x: i32, y: i32) -> i32 { x + y }

fn sub_int (x: i32, y: i32) -> i32 { x - y }

fn mul_int (x: i32, y: i32) -> i32 { x * y }

fn div_int (x: i32, y: i32) -> i32 { x / y }

fn rem_int (x: i32, y: i32) -> i32 { x % y }

fn shr_int (x: i32, y: i32) -> i32 { x >> y }

fn shl_int (x: i32, y: i32) -> i32 { x << y }

fn bitand_int (x: i32, y: i32) -> i32 { x & y }

fn bitand_bool (x : bool, y: bool) -> bool { x & y }

fn bitor_int (x: i32, y: i32) -> i32 { x | y }

fn bitor_bool (x : bool, y: bool) -> bool { x | y }

fn bitxor_int (x: i32, y: i32) -> i32 { x ^ y }

fn bitxor_bool (x: bool, y: bool) -> bool { x ^ y }

fn logical_op_and (x: bool, y: bool) -> bool { x && y }

fn logical_op_or (x: bool, y: bool) -> bool { x || y }

fn eq_int(x : i32, y: i32) -> bool { x == y }

fn eq_bool(x : bool, y: bool) -> bool { x == y }

fn lt_int(x : i32, y: i32) -> bool { x < y }

fn le_int(x : i32, y: i32) -> bool { x <= y }

fn gt_int(x : i32, y: i32) -> bool { x > y }

fn ge_int(x : i32, y: i32) -> bool { x >= y }

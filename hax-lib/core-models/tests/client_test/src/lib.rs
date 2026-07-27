//! Regression-testing crate for the `core-models` Lean library.
//!
//! Each function below exercises an item — either from `core::*` /
//! `std::*` directly, or from the local `core_models::*` source. Aeneas
//! extracts this crate (resolving `std::*` / `core::*` references
//! through its builtin name map) and we compile the result against our
//! hand-written `Aeneas` library. Anything missing in our shims surfaces
//! here as a Lean elaboration error.

#![allow(dead_code)]

// ----- Option ---------------------------------------------------------------

pub fn option_unwrap(x: Option<u8>) -> u8 {
    x.unwrap()
}

pub fn option_unwrap_or(x: Option<u8>, default: u8) -> u8 {
    x.unwrap_or(default)
}

pub fn option_is_some(x: Option<u32>) -> bool {
    x.is_some()
}

pub fn option_is_none(x: Option<u32>) -> bool {
    x.is_none()
}

pub fn option_take(x: &mut Option<u16>) -> Option<u16> {
    x.take()
}

pub fn option_pattern(x: Option<u8>) -> u8 {
    match x {
        Some(v) => v,
        None => 0,
    }
}

pub fn option_double(x: Option<u8>) -> u8 {
    match x {
        Some(v) => v.wrapping_add(v),
        None => 0,
    }
}

// ----- Result ---------------------------------------------------------------

pub fn result_ok(x: Result<u8, u8>) -> Option<u8> {
    x.ok()
}

pub fn result_err(x: Result<u8, u32>) -> Option<u32> {
    x.err()
}

pub fn result_is_ok(x: Result<u8, u8>) -> bool {
    x.is_ok()
}

pub fn result_is_err(x: Result<u8, u8>) -> bool {
    x.is_err()
}

pub fn result_pattern(x: Result<u8, u8>) -> u8 {
    match x {
        Ok(v) => v,
        Err(_) => 0,
    }
}

// ----- mem ------------------------------------------------------------------

pub fn mem_swap_u32(a: &mut u32, b: &mut u32) {
    core::mem::swap(a, b);
}

pub fn mem_replace_u8(dst: &mut u8, src: u8) -> u8 {
    core::mem::replace(dst, src)
}

// ----- Scalar arithmetic ----------------------------------------------------

pub fn add_u8(x: u8, y: u8) -> u8 {
    x + y
}

pub fn sub_u32(x: u32, y: u32) -> u32 {
    x - y
}

pub fn mul_u16(x: u16, y: u16) -> u16 {
    x * y
}

// ----- Comparisons ----------------------------------------------------------

pub fn lt_u8(x: u8, y: u8) -> bool {
    x < y
}

pub fn ge_usize(x: usize, y: usize) -> bool {
    x >= y
}

// ----- Bitwise --------------------------------------------------------------

pub fn xor_u64(x: u64, y: u64) -> u64 {
    x ^ y
}

pub fn or_u32(x: u32, y: u32) -> u32 {
    x | y
}

pub fn and_u8(x: u8, y: u8) -> u8 {
    x & y
}

// ----- Clone / Copy ---------------------------------------------------------

pub fn clone_u64(x: u64) -> u64 {
    x.clone()
}

pub fn copy_u8(x: u8) -> (u8, u8) {
    (x, x)
}

// ----- Arrays ---------------------------------------------------------------

pub fn arr_index(a: [u32; 4], i: usize) -> u32 {
    a[i]
}

pub fn arr_set(mut a: [u32; 4], i: usize, x: u32) -> [u32; 4] {
    a[i] = x;
    a
}

pub fn arr_repeat() -> [u8; 16] {
    [0u8; 16]
}

pub fn arr_to_slice(a: &[u32; 4]) -> &[u32] {
    a
}

/// Triggers `Array.make` with a 24-element initializer (regression test for
/// the default proof tactic — `by rfl` cannot reduce `(Usize.ofNat 24).val`
/// to `24`, only `by simp` with the right lemmas can).
pub const ROUND_CONSTANTS: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808a,
    0x8000000080008000,
    0x000000000000808b,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008a,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000a,
    0x000000008000808b,
    0x800000000000008b,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800a,
    0x800000008000000a,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

/// Direct usage of `std::array::from_fn` — exercises the `Fn`/`FnMut`
/// trait dispatch. The std signature is `F: FnMut`; Aeneas's name map
/// reaches into the `Fn` instance via its `.FnMutInst` super-trait
/// projection, so our `core.ops.function.Fn` structure must expose that
/// field.
pub fn array_from_fn<T, F: Fn(usize) -> T>(f: F) -> [T; 10] {
    std::array::from_fn(f)
}

/// Closure as `Fn` — defines a closure inline and feeds it to
/// `array_from_fn`. Hits the auto-derived `core.ops.function.Fn` impl
/// for closures.
pub fn array_from_fn_closure() -> [usize; 10] {
    std::array::from_fn(|x: usize| x)
}

/// Array indexing returning a reference — covers `<[T; N] as Index<usize>>::index`.
pub fn array_index_ref(a: &[u8; 10], i: usize) -> &u8 {
    &a[i]
}

/// Array indexing returning by value (Copy types).
pub fn array_index_val(a: [u32; 4], i: usize) -> u32 {
    a[i]
}

// ----- Slices ---------------------------------------------------------------

pub fn slice_len(x: &[u8]) -> usize {
    x.len()
}

// NOTE: slice indexing through `SliceIndex` is currently excluded from
// our extraction (see `CHARON_EXCLUDES` in the parent Makefile).
// Re-enable the tests below once the full SliceIndex modeling lands
// (`Sealed` super-trait, `get_mut`/`index_mut` back-edges, raw-pointer
// `get_unchecked*`).
//
//   pub fn slice_index_usize(x: &[u8]) -> u8         { x[0] }
//   pub fn slice_index_range(x: &[u8]) -> &[u8]      { &x[1..3] }
//   pub fn slice_index_range_from(x: &[u8]) -> &[u8] { &x[2..] }
//   pub fn slice_index_range_to(x: &[u8]) -> &[u8]   { &x[..3] }
//   pub fn slice_index_range_full(x: &[u8]) -> &[u8] { &x[..] }

// ----- Range iteration ------------------------------------------------------

/// Exercises `core::iter::range::IteratorRange::next` (the iterator that
/// drives `for i in 0..n` loops over `Range<usize>`).
pub fn range_sum(n: usize) -> usize {
    let mut acc: usize = 0;
    for i in 0..n {
        acc = acc.wrapping_add(i);
    }
    acc
}

// ----- Closures and higher-order --------------------------------------------

pub fn call_fn<F: Fn(u8) -> u8>(f: F, x: u8) -> u8 {
    f(x)
}

pub fn call_fn_mut<F: FnMut(u8) -> u8>(mut f: F, x: u8) -> u8 {
    f(x)
}

// ----- alloc::vec::Vec ------------------------------------------------------
//
// Same gating as slices: `Vec::index` is excluded via ALLOC_CHARON_EXCLUDES.
//
//   pub fn vec_index_usize(x: &Vec<usize>) -> usize { x[0] }
//   pub fn vec_index_and_len(x: Vec<usize>) -> usize { x[0] + x.len() }
//   pub fn vec_index_range(x: &Vec<u8>) -> &[u8] { &x[1..3] }

// --- pure shape (Aeneas marks `~can_fail:false ~lift:false`) ---

pub fn vec_new() -> Vec<u32> {
    Vec::new()
}

pub fn vec_with_capacity(c: usize) -> Vec<u8> {
    Vec::with_capacity(c)
}

pub fn vec_len(v: &Vec<u32>) -> usize {
    v.len()
}

// --- monadic shape (push/insert/resize/extend_from_slice) ---

pub fn vec_push(mut v: Vec<u32>, x: u32) -> Vec<u32> {
    v.push(x);
    v
}

pub fn vec_push_two(mut v: Vec<u8>, x: u8, y: u8) -> Vec<u8> {
    v.push(x);
    v.push(y);
    v
}

pub fn vec_insert(mut v: Vec<u8>, i: usize, x: u8) -> Vec<u8> {
    v.insert(i, x);
    v
}

pub fn vec_extend_from_slice(mut v: Vec<u8>, s: &[u8]) -> Vec<u8> {
    v.extend_from_slice(s);
    v
}

/// `vec![x; n]` lowers to a call to `alloc::vec::from_elem`.
pub fn vec_from_elem(x: u32, n: usize) -> Vec<u32> {
    vec![x; n]
}

// ----- alloc::slice methods -------------------------------------------------
//
// `[T]::to_vec` is in Aeneas's builtin map.

pub fn slice_to_vec(s: &[u8]) -> Vec<u8> {
    s.to_vec()
}

// ----- alloc::boxed::Box ----------------------------------------------------
//
// Hax/Aeneas erase `Box<T>` to `T`, but we still want to make sure the
// surface compiles end-to-end.

pub fn box_new(x: u32) -> Box<u32> {
    Box::new(x)
}

pub fn box_deref(b: &Box<u8>) -> u8 {
    **b
}

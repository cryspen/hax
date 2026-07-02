//! # Loop Equivalence
//!
//! This example demonstrates how the **hax** toolchain can prove that two
//! loops written in different styles compute the same result. The functions
//! [`f`] and [`g`] both apply [`op`] to every element of an array, but they
//! differ in structure:
//!
//! - [`f`] uses a simple element-by-element loop.
//! - [`g`] uses a 2× unrolled loop (processing pairs of elements), with a
//!   fixup step when the array length is odd.

use hax_lib::*;

/// A placeholder operation to apply to every element
fn op(u: u64) -> u64 {
    u / 2
}

/// Straightforward loop: applies [`op`] to each element in order.
fn f<const N: usize>(mut arr: [u64; N]) -> [u64; N] {
    let initial = arr.clone();

    for i in 0..N {
        arr[i] = op(arr[i]);
    }
    arr
}

/// Unrolled loop: processes two elements per iteration, then handles the
/// leftover element when `N` is odd. This computes the same result as [`f`].
///
/// Postcondition: its output equals the result of `f` on the same input.
#[hax_lib::ensures(|_| future(arr) == &f(*arr))]
fn g<const N: usize>(arr: &mut [u64; N]) {
    let initial = arr.clone();

    for i in 0..(N / 2) {
        arr[2 * i] = op(arr[2 * i]);
        arr[2 * i + 1] = op(arr[2 * i + 1]);
    }
    if N % 2 > 0 {
        arr[N - 1] = op(arr[N - 1])
    }
}

// Loop invariant for `f`: after `i` iterations, elements below `i` have been
// transformed by `op`, while elements at index `i` and above are unchanged.
fn f_loop_inv<const N: usize>(arr: &[u64; N], _initial: &[u64; N], i: usize, j: usize) -> bool {
    if j < i {
        arr[j] == op(_initial[j])
    } else if j < N {
        arr[j] == _initial[j]
    } else {
        true
    }
}

// Loop invariant for `g`: after `i` iterations of the unrolled loop, elements
// below `2*i` have been transformed by `op`, the rest are unchanged.
fn g_loop_inv<const N: usize>(arr: &[u64; N], _initial: &[u64; N], i: usize, j: usize) -> bool {
    if j < 2 * i {
        arr[j] == op(_initial[j])
    } else if j < N {
        arr[j] == _initial[j]
    } else {
        true
    }
}

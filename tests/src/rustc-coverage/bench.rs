//! @fail(tc): fstar(2), lean(1), proverif(2)
#![feature(test)]
//@ edition: 2021
//@ compile-flags: --test

extern crate test;

#[bench]
fn my_bench(_b: &mut test::Bencher) {}

module Rust_primitives.Hax.Int

open Rust_primitives

unfold let from_machine (#t:inttype) (x:int_t t) : range_t t = v #t x
unfold let into_machine (#t:inttype) (n:range_t t) : int_t t = mk_int #t n

/// Division on `hax_lib::int::Int`. It truncates towards zero, whereas
/// F*'s `/` on `int` is Euclidean.
unfold let div (x: int) (y: nonzero) : int =
  let q = (if x >= 0 then x else - x) / (if y >= 0 then y else - y) in
  if (x >= 0) = (y >= 0) then q else - q

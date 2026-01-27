module Rust_primitives.Mem

open FStar.Mul

let replace (#t: Type0) (s: t) (src: t) = src
let copy (#t: Type0) (x: t) = x
